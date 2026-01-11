#!/usr/bin/env python3
import argparse
import gzip
import json
import os
from typing import Any, Dict, Iterable, List, Tuple

import json_stream


# Json.compress emits "kind":"<value>" with no whitespace.
KIND_LABELS_STR = {
    "term": "term_nodes",
    "partialTerm": "partial_term_nodes",
    "tactic": "tactic_nodes",
    "command": "command_nodes",
    "macroExpansion": "macro_expansion_nodes",
    "option": "option_nodes",
    "errorName": "error_name_nodes",
    "field": "field_nodes",
    "completion.dot": "completion_dot_nodes",
    "completion.id": "completion_id_nodes",
    "completion.dotId": "completion_dot_id_nodes",
    "completion.fieldId": "completion_field_id_nodes",
    "completion.namespaceId": "completion_namespace_id_nodes",
    "completion.option": "completion_option_nodes",
    "completion.errorName": "completion_error_name_nodes",
    "completion.endSection": "completion_end_section_nodes",
    "completion.tactic": "completion_tactic_nodes",
    "userWidget": "user_widget_nodes",
    "custom": "custom_nodes",
    "fvarAlias": "fvar_alias_nodes",
    "fieldRedecl": "field_redecl_nodes",
    "delabTerm": "delab_term_nodes",
    "choice": "choice_nodes",
    "doc": "doc_nodes",
    "docElab": "doc_elab_nodes",
}
TREE_KINDS_STR = {"node", "context", "hole", "truncated"}


def iter_json_files(root: str) -> Iterable[str]:
    for dirpath, _dirnames, filenames in os.walk(root):
        for name in filenames:
            if name.endswith(".json") or name.endswith(".json.gz"):
                yield os.path.join(dirpath, name)


def output_path_for_json(root: str, json_path: str) -> str:
    rel = os.path.relpath(json_path, root)
    if rel.endswith(".json.gz"):
        rel = rel[:-8]
    elif rel.endswith(".json"):
        rel = rel[:-5]
    return rel + ".lean"


def open_text_maybe_gzip(path: str):
    if path.endswith(".gz"):
        return gzip.open(path, "rt", encoding="utf-8")
    return open(path, "rt", encoding="utf-8")


def walk_json_stream(value: Any, counts: Dict[str, int]) -> None:
    if isinstance(value, str):
        return
    if hasattr(value, "items"):
        for key, item in value.items():
            if key == "kind" and isinstance(item, str):
                label = KIND_LABELS_STR.get(item)
                if label:
                    counts[label] += 1
                if item in TREE_KINDS_STR:
                    counts["total_nodes"] += 1
            walk_json_stream(item, counts)
        return
    if hasattr(value, "__iter__") and not isinstance(value, (bytes, bytearray)):
        for item in value:
            walk_json_stream(item, counts)


def count_with_json_stream(path: str) -> Dict[str, int]:
    counts = {name: 0 for name in KIND_LABELS_STR.values()}
    counts["total_nodes"] = 0
    with open_text_maybe_gzip(path) as handle:
        data = json_stream.load(handle)
        walk_json_stream(data, counts)
    return counts


def count_patterns(path: str) -> Dict[str, int]:
    return count_with_json_stream(path)


def build_metrics(root: str) -> List[Dict[str, object]]:
    records: List[Tuple[str, Dict[str, int]]] = []
    for path in iter_json_files(root):
        print(f"[infotree_metrics] start {path}")
        counts = count_patterns(path)
        rel = output_path_for_json(root, path)
        records.append((rel, counts))
    records.sort(key=lambda item: item[0])
    return [
        {"path": path, **counts}
        for path, counts in records
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Aggregate infotree metrics per file.")
    parser.add_argument("--root", required=True, help="Directory containing infotree JSON outputs.")
    parser.add_argument("--out", required=True, help="Output JSON file.")
    args = parser.parse_args()

    records = build_metrics(args.root)
    output = {
        "root": os.path.abspath(args.root),
        "files": records,
    }
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as handle:
        json.dump(output, handle, ensure_ascii=True)


if __name__ == "__main__":
    main()
