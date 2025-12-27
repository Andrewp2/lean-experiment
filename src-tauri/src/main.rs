#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use notify::{RecursiveMode, Watcher};
use regex::Regex;
use serde::Serialize;
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
    sync::{
        mpsc::{channel, Sender},
        Mutex,
    },
    time::{Duration, Instant},
};
use tauri::{Emitter, State};
use walkdir::WalkDir;

const MAX_DEPTH: usize = 5;
const MIN_PERCENT: f64 = 0.01;
const GROUP_BY_KEY: &str = "loc";

struct WatchHandle {
    stop_tx: Sender<()>,
    thread: std::thread::JoinHandle<()>,
}

#[derive(Default)]
struct WatchState(Mutex<Option<WatchHandle>>);

#[derive(Serialize, Clone)]
struct TreemapOutput {
    root: TreemapNode,
    #[serde(rename = "seriesKeys")]
    series_keys: Vec<String>,
}

#[derive(Serialize, Clone)]
struct RebuildStatus {
    status: String,
}

#[derive(Serialize, Clone)]
struct TreemapNode {
    name: String,
    path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    children: Option<Vec<TreemapNode>>,
    series: HashMap<String, f64>,
}

#[derive(Clone)]
struct BuildNode {
    name: String,
    path: String,
    children: HashMap<String, BuildNode>,
    size: u64,
    count: u64,
    loc: u64,
    comment_lines: u64,
    code_lines: u64,
    porting_notes: u64,
    adaptation_notes: u64,
    note_total: u64,
    regex_counts: HashMap<String, u64>,
}

struct RegexPattern {
    key: String,
    regex: Regex,
}

struct FileMetrics {
    loc: u64,
    comment_lines: u64,
    code_lines: u64,
    porting_notes: u64,
    adaptation_notes: u64,
    note_total: u64,
    regex_counts: HashMap<String, u64>,
}

fn make_root_node() -> BuildNode {
    BuildNode {
        name: "Mathlib".to_string(),
        path: "Mathlib".to_string(),
        children: HashMap::new(),
        size: 0,
        count: 0,
        loc: 0,
        comment_lines: 0,
        code_lines: 0,
        porting_notes: 0,
        adaptation_notes: 0,
        note_total: 0,
        regex_counts: HashMap::new(),
    }
}

fn analyze_lean_content(
    content: &str,
    porting_note_regex: &Regex,
    adaptation_note_regex: &Regex,
    regex_patterns: &[RegexPattern],
) -> FileMetrics {
    let lines: Vec<&str> = content.lines().collect();
    let loc = lines.len() as u64;
    let porting_notes = porting_note_regex.find_iter(content).count() as u64;
    let adaptation_notes = adaptation_note_regex.find_iter(content).count() as u64;
    let mut regex_counts = HashMap::new();
    for pattern in regex_patterns {
        let count = pattern.regex.find_iter(content).count() as u64;
        regex_counts.insert(pattern.key.clone(), count);
    }
    let mut comment_lines = 0;
    let mut in_block = false;
    for line in &lines {
        let trimmed = line.trim();
        if in_block {
            comment_lines += 1;
            if trimmed.contains("-/") {
                in_block = false;
            }
            continue;
        }
        if trimmed.starts_with("--") {
            comment_lines += 1;
            continue;
        }
        if trimmed.contains("/-") {
            comment_lines += 1;
            if !trimmed.contains("-/") {
                in_block = true;
            }
        }
    }
    let code_lines = loc.saturating_sub(comment_lines);
    let note_total = porting_notes + adaptation_notes;
    FileMetrics {
        loc,
        comment_lines,
        code_lines,
        porting_notes,
        adaptation_notes,
        note_total,
        regex_counts,
    }
}

fn add_build_file(
    root: &mut BuildNode,
    relative_path: &str,
    size: u64,
    metrics: FileMetrics,
) {
    let mut parts: Vec<&str> = relative_path.split('/').filter(|p| !p.is_empty()).collect();
    if parts.first() == Some(&"Mathlib") {
        parts.remove(0);
    }
    let file_name = parts.pop();
    if file_name.is_none() {
        return;
    }
    let base_name = file_name.unwrap().trim_end_matches(".lean");
    let mut segments: Vec<&str> = parts;
    segments.push(base_name);
    let depth = std::cmp::min(segments.len(), MAX_DEPTH);

    let FileMetrics {
        loc,
        comment_lines,
        code_lines,
        porting_notes,
        adaptation_notes,
        note_total,
        regex_counts,
    } = metrics;
    let mut node = root;
    node.size += size;
    node.count += 1;
    node.loc += loc;
    node.comment_lines += comment_lines;
    node.code_lines += code_lines;
    node.porting_notes += porting_notes;
    node.adaptation_notes += adaptation_notes;
    node.note_total += note_total;
    for (key, value) in &regex_counts {
        *node.regex_counts.entry(key.clone()).or_insert(0) += value;
    }

    for i in 0..depth {
        let name = segments[i];
        let child = node
            .children
            .entry(name.to_string())
            .or_insert_with(|| BuildNode {
                name: name.to_string(),
                path: format!("{}/{}", node.path, name),
                children: HashMap::new(),
                size: 0,
                count: 0,
                loc: 0,
                comment_lines: 0,
                code_lines: 0,
                porting_notes: 0,
                adaptation_notes: 0,
                note_total: 0,
                regex_counts: HashMap::new(),
            });
        child.size += size;
        child.count += 1;
        child.loc += loc;
        child.comment_lines += comment_lines;
        child.code_lines += code_lines;
        child.porting_notes += porting_notes;
        child.adaptation_notes += adaptation_notes;
        child.note_total += note_total;
        for (key, value) in &regex_counts {
            *child.regex_counts.entry(key.clone()).or_insert(0) += value;
        }
        node = child;
    }
}

fn to_treemap_node(node: &BuildNode) -> TreemapNode {
    let children: Vec<TreemapNode> = node.children.values().map(to_treemap_node).collect();
    let comment_ratio = if node.code_lines > 0 {
        node.comment_lines as f64 / node.code_lines as f64
    } else {
        0.0
    };
    let mut series = HashMap::new();
    series.insert("bytes".to_string(), node.size as f64);
    series.insert("file_count".to_string(), node.count as f64);
    series.insert("loc".to_string(), node.loc as f64);
    series.insert("comment_lines".to_string(), node.comment_lines as f64);
    series.insert("code_lines".to_string(), node.code_lines as f64);
    series.insert("comment_ratio".to_string(), comment_ratio);
    series.insert("porting_notes".to_string(), node.porting_notes as f64);
    series.insert("adaptation_notes".to_string(), node.adaptation_notes as f64);
    series.insert("notes_total".to_string(), node.note_total as f64);
    for (key, value) in &node.regex_counts {
        series.insert(key.clone(), *value as f64);
    }
    TreemapNode {
        name: node.name.clone(),
        path: node.path.clone(),
        children: if children.is_empty() {
            None
        } else {
            Some(children)
        },
        series,
    }
}

fn sum_series_value(node: &TreemapNode, key: &str) -> f64 {
    if let Some(value) = node.series.get(key) {
        return *value;
    }
    node.children
        .as_ref()
        .map(|children| {
            children
                .iter()
                .map(|child| sum_series_value(child, key))
                .sum()
        })
        .unwrap_or(0.0)
}

fn normalize_node(node: TreemapNode) -> TreemapNode {
    let children = match node.children {
        Some(children) => children,
        None => return node,
    };
    let normalized_children: Vec<TreemapNode> = children.into_iter().map(normalize_node).collect();
    let key = if node.series.contains_key(GROUP_BY_KEY) {
        GROUP_BY_KEY
    } else {
        "bytes"
    };
    let total: f64 = normalized_children
        .iter()
        .map(|child| sum_series_value(child, key))
        .sum();
    if total == 0.0 {
        return TreemapNode {
            children: Some(normalized_children),
            ..node
        };
    }
    let mut keep = Vec::new();
    let mut other_children = Vec::new();
    for child in normalized_children {
        let value = sum_series_value(&child, key);
        if value / total < MIN_PERCENT {
            other_children.push(child);
        } else {
            keep.push(child);
        }
    }
    if other_children.is_empty() || keep.is_empty() {
        return TreemapNode {
            children: Some(keep.into_iter().chain(other_children).collect()),
            ..node
        };
    }

    let mut series_keys = HashSet::new();
    for child in &other_children {
        for key in child.series.keys() {
            series_keys.insert(key.clone());
        }
    }
    let mut other_series = HashMap::new();
    for key in &series_keys {
        let sum: f64 = other_children
            .iter()
            .map(|child| sum_series_value(child, key))
            .sum();
        other_series.insert(key.clone(), sum);
    }
    let other_node = normalize_node(TreemapNode {
        name: "Miscellaneous".to_string(),
        path: format!("{}/Miscellaneous", node.path),
        children: Some(other_children),
        series: other_series,
    });

    keep.push(other_node);
    TreemapNode {
        children: Some(keep),
        ..node
    }
}

fn make_regex_key(pattern: &str) -> String {
    format!("regex:{}", pattern)
}

fn compile_regex_patterns(patterns: &[String]) -> Result<Vec<RegexPattern>, String> {
    let mut compiled = Vec::new();
    for pattern in patterns {
        if pattern.trim().is_empty() {
            continue;
        }
        let regex =
            Regex::new(pattern).map_err(|error| format!("Regex error: {}", error))?;
        compiled.push(RegexPattern {
            key: make_regex_key(pattern),
            regex,
        });
    }
    Ok(compiled)
}

fn build_treemap(mathlib_path: &Path, regex_patterns: &[String]) -> Result<TreemapOutput, String> {
    let start_time = Instant::now();
    let root_dir = mathlib_path
        .canonicalize()
        .map_err(|error| format!("Failed to open {}: {}", mathlib_path.display(), error))?;
    let mathlib_dir = if root_dir.join("Mathlib").is_dir() {
        root_dir.join("Mathlib")
    } else {
        root_dir.clone()
    };

    let porting_note_regex =
        Regex::new(r"(?i)porting[\s_-]*note").map_err(|error| format!("Regex error: {}", error))?;
    let adaptation_note_regex =
        Regex::new(r"(?i)#adaptation_note\b").map_err(|error| format!("Regex error: {}", error))?;
    let compiled_regexes = compile_regex_patterns(regex_patterns)?;

    let mut root = make_root_node();
    for entry in WalkDir::new(&mathlib_dir)
        .into_iter()
        .filter_map(Result::ok)
    {
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("lean") {
            continue;
        }
        let content = fs::read_to_string(path)
            .map_err(|error| format!("Failed to read {}: {}", path.display(), error))?;
        let size = entry
            .metadata()
            .map_err(|error| format!("Failed to stat {}: {}", path.display(), error))?
            .len();
        let metrics = analyze_lean_content(
            &content,
            &porting_note_regex,
            &adaptation_note_regex,
            &compiled_regexes,
        );
        let relative = path
            .strip_prefix(&root_dir)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        add_build_file(&mut root, &relative, size, metrics);
    }

    let output_root = normalize_node(to_treemap_node(&root));
    let mut series_keys = HashSet::new();
    fn collect_keys(node: &TreemapNode, keys: &mut HashSet<String>) {
        for key in node.series.keys() {
            keys.insert(key.clone());
        }
        if let Some(children) = &node.children {
            for child in children {
                collect_keys(child, keys);
            }
        }
    }
    collect_keys(&output_root, &mut series_keys);
    let mut series_keys_vec: Vec<String> = series_keys.into_iter().collect();
    series_keys_vec.sort();
    eprintln!(
        "Treemap build completed in {}ms",
        start_time.elapsed().as_millis()
    );
    Ok(TreemapOutput {
        root: output_root,
        series_keys: series_keys_vec,
    })
}

#[tauri::command]
fn scan_mathlib(path: String, regex_patterns: Option<Vec<String>>) -> Result<TreemapOutput, String> {
    let patterns = regex_patterns.unwrap_or_default();
    build_treemap(Path::new(&path), &patterns)
}

#[tauri::command]
fn start_mathlib_watch(
    path: String,
    debounce_ms: Option<u64>,
    regex_patterns: Option<Vec<String>>,
    app: tauri::AppHandle,
    state: State<WatchState>,
) -> Result<(), String> {
    let path_buf = PathBuf::from(&path);
    if !path_buf.is_dir() {
        return Err(format!("{} is not a directory", path));
    }
    let debounce = Duration::from_millis(debounce_ms.unwrap_or(1200));

    if let Some(handle) = state.0.lock().unwrap().take() {
        let _ = handle.stop_tx.send(());
        let _ = handle.thread.join();
    }

    let (stop_tx, stop_rx) = channel();
    let app_handle = app.clone();
    let patterns = regex_patterns.unwrap_or_default();
    let thread = std::thread::spawn(move || {
        eprintln!("Watching {} for changes...", path_buf.display());
        let (event_tx, event_rx) = channel();
        let mut watcher = match notify::recommended_watcher(move |res| {
            let _ = event_tx.send(res);
        }) {
            Ok(watcher) => watcher,
            Err(error) => {
                eprintln!("Failed to create watcher: {}", error);
                return;
            }
        };
        if let Err(error) = watcher.watch(&path_buf, RecursiveMode::Recursive) {
            eprintln!("Failed to watch {}: {}", path_buf.display(), error);
            return;
        }

        let mut pending = false;
        let mut last_event = Instant::now();
        loop {
            if stop_rx.try_recv().is_ok() {
                break;
            }
            match event_rx.recv_timeout(Duration::from_millis(200)) {
                Ok(Ok(event)) => {
                    eprintln!("Watch event: {:?}", event.kind);
                    pending = true;
                    last_event = Instant::now();
                }
                Ok(Err(error)) => {
                    eprintln!("Watcher error: {}", error);
                }
                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {}
                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
            }
            if pending && last_event.elapsed() >= debounce {
                eprintln!("Rebuilding treemap after changes...");
                let _ = app_handle.emit(
                    "mathlib:treemap-rebuild",
                    RebuildStatus {
                        status: "start".to_string(),
                    },
                );
                if let Ok(output) = build_treemap(&path_buf, &patterns) {
                    let _ = app_handle.emit("mathlib:treemap-updated", output);
                }
                let _ = app_handle.emit(
                    "mathlib:treemap-rebuild",
                    RebuildStatus {
                        status: "end".to_string(),
                    },
                );
                pending = false;
            }
        }
    });

    state
        .0
        .lock()
        .unwrap()
        .replace(WatchHandle { stop_tx, thread });
    Ok(())
}

#[tauri::command]
fn stop_mathlib_watch(state: State<WatchState>) -> Result<(), String> {
    if let Some(handle) = state.0.lock().unwrap().take() {
        let _ = handle.stop_tx.send(());
        let _ = handle.thread.join();
    }
    Ok(())
}

#[tauri::command]
fn open_external(url: String) -> Result<(), String> {
    open::that(url).map_err(|error| error.to_string())?;
    Ok(())
}

fn main() {
    tauri::Builder::default()
        .plugin(tauri_plugin_dialog::init())
        .manage(WatchState::default())
        .invoke_handler(tauri::generate_handler![
            scan_mathlib,
            start_mathlib_watch,
            stop_mathlib_watch,
            open_external
        ])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
