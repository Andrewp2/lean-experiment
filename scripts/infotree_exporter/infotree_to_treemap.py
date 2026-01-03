#!/usr/bin/env python3
import argparse
import json
import os
import sys


def build_entries(input_dir):
    entries = []
    for root_dir, _dirs, files in os.walk(input_dir):
        for name in files:
            if not name.endswith(".json"):
                continue
            file_path = os.path.join(root_dir, name)
            rel_path = os.path.relpath(file_path, input_dir).replace("\\", "/")
            node_path = rel_path[:-5] if rel_path.endswith(".json") else rel_path
            try:
                with open(file_path, "r", encoding="utf-8") as handle:
                    data = json.load(handle)
            except Exception as exc:
                print(f"[infotree_to_treemap] Failed to read {file_path}: {exc}", file=sys.stderr)
                continue
            metrics = data.get("metrics")
            if not isinstance(metrics, dict):
                continue
            entries.append({"path": node_path, "series": metrics})
    return entries


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input-dir", required=True)
    parser.add_argument("--output-file", required=True)
    args = parser.parse_args()

    input_dir = os.path.abspath(args.input_dir)
    if not os.path.isdir(input_dir):
        raise SystemExit(f"Missing input dir: {input_dir}")

    entries = build_entries(input_dir)
    entries.sort(key=lambda entry: entry["path"])
    payload = {"entries": entries}

    output_dir = os.path.dirname(os.path.abspath(args.output_file))
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(args.output_file, "w", encoding="utf-8") as handle:
        json.dump(payload, handle)
    print(f"[infotree_to_treemap] wrote {len(entries)} entries to {args.output_file}")


if __name__ == "__main__":
    raise SystemExit(main())
