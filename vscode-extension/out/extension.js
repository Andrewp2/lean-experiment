"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode = __importStar(require("vscode"));
const promises_1 = require("node:fs/promises");
const node_path_1 = __importDefault(require("node:path"));
const WEBVIEW_DIST = 'media';
const WEBVIEW_ENTRY = 'pages/mathlib-vscode.html';
const MAX_DEPTH = 5;
const MIN_PERCENT = 0.01;
const GROUP_BY = 'loc';
const portingNoteRegex = /porting[\s_-]*note/gi;
const adaptationNoteRegex = /#adaptation_note\b/gi;
const makeRegexKey = (pattern) => `regex:${pattern}`;
const compileRegexPatterns = (patterns) => {
    const compiled = [];
    patterns.forEach((pattern) => {
        const trimmed = pattern.trim();
        if (!trimmed) {
            return;
        }
        try {
            compiled.push({ pattern: trimmed, key: makeRegexKey(trimmed), regex: new RegExp(trimmed, 'g') });
        }
        catch (error) {
            void vscode.window.showWarningMessage(`Invalid regex: ${trimmed}`);
            console.warn('Invalid regex pattern', trimmed, error);
        }
    });
    return compiled;
};
const analyzeLeanContent = (content, regexPatterns) => {
    const lines = content.split(/\r\n|\r|\n/);
    const loc = lines.length;
    const portingNotes = Array.from(content.matchAll(portingNoteRegex)).length;
    const adaptationNotes = Array.from(content.matchAll(adaptationNoteRegex)).length;
    const regexCounts = {};
    regexPatterns.forEach(({ key, regex }) => {
        regexCounts[key] = content.match(regex)?.length ?? 0;
    });
    let commentLines = 0;
    let inBlock = false;
    for (const line of lines) {
        const trimmed = line.trim();
        if (inBlock) {
            commentLines += 1;
            if (trimmed.includes('-/')) {
                inBlock = false;
            }
            continue;
        }
        if (trimmed.startsWith('--')) {
            commentLines += 1;
            continue;
        }
        if (trimmed.includes('/-')) {
            commentLines += 1;
            if (!trimmed.includes('-/')) {
                inBlock = true;
            }
        }
    }
    const codeLines = Math.max(0, loc - commentLines);
    return {
        loc,
        commentLines,
        codeLines,
        portingNotes,
        adaptationNotes,
        noteTotal: portingNotes + adaptationNotes,
        regexCounts,
    };
};
const makeRootNode = () => ({
    name: 'Mathlib',
    path: 'Mathlib',
    children: new Map(),
    size: 0,
    count: 0,
    loc: 0,
    commentLines: 0,
    codeLines: 0,
    portingNotes: 0,
    adaptationNotes: 0,
    noteTotal: 0,
    regexCounts: {},
});
const addBuildFile = (root, relativePath, size, metrics) => {
    const parts = relativePath.split('/').filter(Boolean);
    if (parts[0] === 'Mathlib') {
        parts.shift();
    }
    const fileName = parts.pop();
    if (!fileName) {
        return;
    }
    const baseName = fileName.replace(/\.lean$/, '');
    const segments = [...parts, baseName].filter(Boolean);
    const depth = Math.min(segments.length, MAX_DEPTH);
    let node = root;
    node.size += size;
    node.count += 1;
    node.loc += metrics.loc;
    node.commentLines += metrics.commentLines;
    node.codeLines += metrics.codeLines;
    node.portingNotes += metrics.portingNotes;
    node.adaptationNotes += metrics.adaptationNotes;
    node.noteTotal += metrics.noteTotal;
    Object.entries(metrics.regexCounts).forEach(([key, value]) => {
        node.regexCounts[key] = (node.regexCounts[key] ?? 0) + value;
    });
    for (let i = 0; i < depth; i += 1) {
        const name = segments[i];
        let child = node.children.get(name);
        if (!child) {
            child = {
                name,
                path: node.path ? `${node.path}/${name}` : name,
                children: new Map(),
                size: 0,
                count: 0,
                loc: 0,
                commentLines: 0,
                codeLines: 0,
                portingNotes: 0,
                adaptationNotes: 0,
                noteTotal: 0,
                regexCounts: {},
            };
            node.children.set(name, child);
        }
        child.size += size;
        child.count += 1;
        child.loc += metrics.loc;
        child.commentLines += metrics.commentLines;
        child.codeLines += metrics.codeLines;
        child.portingNotes += metrics.portingNotes;
        child.adaptationNotes += metrics.adaptationNotes;
        child.noteTotal += metrics.noteTotal;
        Object.entries(metrics.regexCounts).forEach(([key, value]) => {
            child.regexCounts[key] = (child.regexCounts[key] ?? 0) + value;
        });
        node = child;
    }
};
const sumSeriesValue = (node, key) => {
    const current = node.series?.[key];
    if (typeof current === 'number') {
        return current;
    }
    return (node.children ?? []).reduce((sum, child) => sum + sumSeriesValue(child, key), 0);
};
const normalizeNode = (node) => {
    if (!node.children || node.children.length === 0) {
        return node;
    }
    const normalizedChildren = node.children.map(normalizeNode);
    const key = node.series?.[GROUP_BY] !== undefined ? GROUP_BY : 'bytes';
    const total = normalizedChildren.reduce((sum, child) => sum + sumSeriesValue(child, key), 0);
    if (total === 0) {
        return { ...node, children: normalizedChildren };
    }
    const keep = [];
    const otherChildren = [];
    for (const child of normalizedChildren) {
        const childValue = sumSeriesValue(child, key);
        if (childValue / total < MIN_PERCENT) {
            otherChildren.push(child);
        }
        else {
            keep.push(child);
        }
    }
    if (otherChildren.length === 0 || keep.length === 0) {
        return { ...node, children: normalizedChildren };
    }
    const seriesKeys = new Set();
    for (const child of otherChildren) {
        Object.keys(child.series ?? {}).forEach((seriesKey) => seriesKeys.add(seriesKey));
    }
    const otherSeries = {};
    for (const seriesKey of seriesKeys) {
        otherSeries[seriesKey] = otherChildren.reduce((sum, child) => sum + sumSeriesValue(child, seriesKey), 0);
    }
    const otherNode = normalizeNode({
        name: 'Miscellaneous',
        path: node.path ? `${node.path}/Miscellaneous` : 'Miscellaneous',
        children: otherChildren,
        series: otherSeries,
    });
    return { ...node, children: [...keep, otherNode] };
};
const toTreemapNode = (node) => {
    const children = Array.from(node.children.values()).map(toTreemapNode);
    const commentRatio = node.codeLines > 0 ? node.commentLines / node.codeLines : 0;
    const series = {
        bytes: node.size,
        file_count: node.count,
        loc: node.loc,
        comment_lines: node.commentLines,
        code_lines: node.codeLines,
        comment_ratio: commentRatio,
        porting_notes: node.portingNotes,
        adaptation_notes: node.adaptationNotes,
        notes_total: node.noteTotal,
        ...node.regexCounts,
    };
    return {
        name: node.name,
        path: node.path,
        children: children.length > 0 ? children : undefined,
        series,
    };
};
const collectKeys = (node, keys) => {
    Object.keys(node.series ?? {}).forEach((key) => keys.add(key));
    node.children?.forEach((child) => collectKeys(child, keys));
};
const normalizeBasePath = (inputPath) => {
    const normalized = node_path_1.default.normalize(inputPath);
    return node_path_1.default.basename(normalized).toLowerCase() === 'mathlib'
        ? node_path_1.default.dirname(normalized)
        : normalized;
};
const resolveMathlibPaths = async (inputPath) => {
    const basePath = normalizeBasePath(inputPath);
    const baseUri = vscode.Uri.file(basePath);
    const mathlibUri = vscode.Uri.joinPath(baseUri, 'Mathlib');
    try {
        const stat = await vscode.workspace.fs.stat(mathlibUri);
        if (stat.type & vscode.FileType.Directory) {
            return { basePath, baseUri, mathlibUri };
        }
    }
    catch {
        // Fall back to the base path if Mathlib doesn't exist.
    }
    return { basePath, baseUri, mathlibUri: baseUri };
};
const buildTreemapFromPath = async (inputPath, regexPatterns) => {
    const { basePath, baseUri, mathlibUri } = await resolveMathlibPaths(inputPath);
    const root = makeRootNode();
    const decoder = new TextDecoder('utf-8');
    const compiledRegexes = compileRegexPatterns(regexPatterns);
    const walk = async (dir) => {
        const entries = await vscode.workspace.fs.readDirectory(dir);
        await Promise.all(entries.map(async ([name, type]) => {
            const entryUri = vscode.Uri.joinPath(dir, name);
            if (type === vscode.FileType.Directory) {
                await walk(entryUri);
                return;
            }
            if (type === vscode.FileType.File && name.endsWith('.lean')) {
                const stats = await vscode.workspace.fs.stat(entryUri);
                const content = decoder.decode(await vscode.workspace.fs.readFile(entryUri));
                const metrics = analyzeLeanContent(content, compiledRegexes);
                const relativePath = node_path_1.default.relative(baseUri.fsPath, entryUri.fsPath).replace(/\\/g, '/');
                addBuildFile(root, relativePath, stats.size, metrics);
            }
        }));
    };
    await walk(mathlibUri);
    const outputRoot = normalizeNode(toTreemapNode(root));
    const seriesKeys = new Set();
    collectKeys(outputRoot, seriesKeys);
    return { root: outputRoot, seriesKeys: Array.from(seriesKeys).sort() };
};
const rewriteWebviewHtml = (html, webview, extensionUri) => {
    const mediaRoot = vscode.Uri.joinPath(extensionUri, WEBVIEW_DIST);
    const withCsp = html.replace('<head>', `<head>
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src ${webview.cspSource} data:; style-src ${webview.cspSource} 'unsafe-inline'; script-src ${webview.cspSource} 'unsafe-inline'; worker-src ${webview.cspSource} blob:; font-src ${webview.cspSource};">`);
    return withCsp.replace(/(href|src)=\"(.+?)\"/g, (match, attr, value) => {
        if (!value.startsWith('./')) {
            return match;
        }
        const resourceUri = webview.asWebviewUri(vscode.Uri.joinPath(mediaRoot, value));
        return `${attr}="${resourceUri.toString()}"`;
    });
};
const openTreemapPanel = async (context) => {
    const panel = vscode.window.createWebviewPanel('mathlibTreemap', 'Mathlib Treemap', vscode.ViewColumn.One, {
        enableScripts: true,
        retainContextWhenHidden: true,
        localResourceRoots: [vscode.Uri.joinPath(context.extensionUri, WEBVIEW_DIST)],
    });
    let isBuilding = false;
    let activeRegexPatterns = [];
    let currentBasePath = null;
    const rebuildTreemap = async (basePath) => {
        if (isBuilding) {
            return;
        }
        isBuilding = true;
        const startedAt = Date.now();
        try {
            await panel.webview.postMessage({ type: 'rebuildStatus', status: 'start' });
            const output = await buildTreemapFromPath(basePath, activeRegexPatterns);
            await panel.webview.postMessage({ type: 'loadJson', text: JSON.stringify(output) });
        }
        catch (error) {
            console.error('Failed to build treemap', error);
            void vscode.window.showWarningMessage('Unable to scan Mathlib files for metrics.');
        }
        finally {
            await panel.webview.postMessage({ type: 'rebuildStatus', status: 'end' });
            const durationMs = Date.now() - startedAt;
            console.log(`[treemap] rebuild completed in ${durationMs}ms`);
            isBuilding = false;
        }
    };
    const detectMathlibPath = async () => {
        const workspaceFolders = vscode.workspace.workspaceFolders ?? [];
        for (const folder of workspaceFolders) {
            const name = folder.name.toLowerCase();
            const fsPath = folder.uri.fsPath;
            if (name === 'mathlib4' || fsPath.endsWith('/mathlib4')) {
                return fsPath;
            }
            if (name === 'mathlib' || fsPath.endsWith('/Mathlib') || fsPath.endsWith('/mathlib')) {
                return fsPath;
            }
            try {
                const stat = await vscode.workspace.fs.stat(vscode.Uri.joinPath(folder.uri, 'Mathlib'));
                if (stat.type & vscode.FileType.Directory) {
                    return fsPath;
                }
            }
            catch {
                // Ignore missing Mathlib directory in this workspace folder.
            }
        }
        return workspaceFolders[0]?.uri.fsPath ?? null;
    };
    try {
        const htmlPath = node_path_1.default.join(context.extensionPath, WEBVIEW_DIST, WEBVIEW_ENTRY);
        const html = await (0, promises_1.readFile)(htmlPath, 'utf8');
        panel.webview.html = rewriteWebviewHtml(html, panel.webview, context.extensionUri);
    }
    catch (error) {
        panel.webview.html = `<html><body><h2>Missing webview assets.</h2><p>Build the webview and run <code>npm run copy-webview</code> from <code>vscode-extension</code>.</p></body></html>`;
        console.error('Failed to load webview HTML', error);
    }
    panel.webview.onDidReceiveMessage(async (message) => {
        if (message?.type === 'openFile' && typeof message.path === 'string') {
            try {
                const uri = vscode.Uri.file(message.path);
                const doc = await vscode.workspace.openTextDocument(uri);
                await vscode.window.showTextDocument(doc, { preview: true });
            }
            catch (error) {
                void vscode.window.showErrorMessage('Unable to open file in VS Code.');
                console.error('Failed to open file', error);
            }
            return;
        }
        if (message?.type === 'pickJson') {
            const selected = await vscode.window.showOpenDialog({
                canSelectMany: false,
                filters: { JSON: ['json'] },
                openLabel: 'Open Metrics JSON',
            });
            const uri = selected?.[0];
            if (!uri) {
                return;
            }
            try {
                const text = await (0, promises_1.readFile)(uri.fsPath, 'utf8');
                await panel.webview.postMessage({ type: 'loadJson', text });
            }
            catch (error) {
                void vscode.window.showErrorMessage('Unable to read JSON file.');
                console.error('Failed to read JSON', error);
            }
        }
        if (message?.type === 'showWarning' && typeof message.text === 'string') {
            void vscode.window.showWarningMessage(message.text);
        }
        if (message?.type === 'setRegexPatterns' && Array.isArray(message.patterns)) {
            activeRegexPatterns = message.patterns.filter((pattern) => (typeof pattern === 'string' && pattern.trim()));
            return;
        }
        if (message?.type === 'setMathlibPath' && typeof message.path === 'string') {
            const nextPath = message.path.trim();
            if (!nextPath) {
                return;
            }
            currentBasePath = normalizeBasePath(nextPath);
            return;
        }
        if (message?.type === 'requestRebuild') {
            const nextPath = typeof message.path === 'string' ? message.path.trim() : '';
            const basePath = nextPath || currentBasePath;
            if (!basePath) {
                void vscode.window.showWarningMessage('Set a Mathlib path before rebuilding.');
                return;
            }
            await rebuildTreemap(basePath);
            return;
        }
        if (message?.type === 'webviewReady') {
            const mathlibPath = await detectMathlibPath();
            if (mathlibPath) {
                void panel.webview.postMessage({ type: 'setMathlibPath', path: mathlibPath });
                currentBasePath = normalizeBasePath(mathlibPath);
            }
        }
    });
};
const activate = (context) => {
    context.subscriptions.push(vscode.commands.registerCommand('leanExperiment.openTreemap', () => {
        void openTreemapPanel(context);
    }));
};
exports.activate = activate;
const deactivate = () => undefined;
exports.deactivate = deactivate;
