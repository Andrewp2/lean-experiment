# Infotree exporter script

This is a script that exports Infotrees from mathlib. It has a python script to do batch processing,
which also limits the memory taken by each file which helps stability.
Expected types are truncated when `expr.sizeWithoutSharing` exceeds the `--max-expected-expr-nodes` limit.
Warning: This script can take multiple hours to run. If you exit in the middle of it running, you'll have to delete
the last JSON file produced. If you just run the same command again, it'll skip past all the files that already
exists and start on the next one.

The script runs a lean script inside systemd to cap the amount of memory used to not crash the operating system.

## Run

```
python3 scripts/infotree_exporter/run_batches.py \
  --root /home/andrew-peterson/code/mathlib4 \
  --out /home/andrew-peterson/code/lean-experiment/infotree_output \
  --start 0 --to-end --batch-size 1 \
  --gzip --skip-on-error --continue  \
  --memory-max 16G --max-expected-expr-nodes 50000 \
  --log-file /home/andrew-peterson/code/lean-experiment/infotree_export.txt
```

Flags:
- **Required paths**: `--root` mathlib4 repo root, `--out` output directory.
- **Batch selection**: `--start` first file index, `--total` number of files, `--to-end` process to end, `--batch-size` files per batch.
- **Timeouts and limits**: `--max-seconds` per-file timeout, `--max-infotree-nodes` cap infotree nodes per file, `--max-expected-expr-nodes` truncate large expected types.
- **Output control**: `--gzip` write `.json.gz`, `--skip-on-error` delete outputs for erroring files, `--continue` skip batches with existing outputs.
- **Metrics export**: `--string-metrics` collect rendered expr/expected/doc sizes, `--string-metrics-csv` append those metrics to CSV.
- **Monitoring**: `--rss-log-mb` print memory stats when RSS exceeds threshold, `--mem-debug` print extra memory diagnostics, `--log-file` tee output to a file.
- **Execution**: `--memory-max` systemd MemoryMax (default 16G), `--no-systemd` run directly, `--systemd-system` use system scope instead of user.

## Import graph

Build an import graph JSON (direct imports plus transitive layers) from Mathlib sources:

```
cd scripts/infotree_exporter
lake build import_graph
./.lake/build/bin/import_graph \
  --root /home/andrew-peterson/code/mathlib4 \
  --out /home/andrew-peterson/code/lean-experiment/import_graph.json \
  --max-depth 4
```

## Infotree proof-size proxies

Counts infotree metrics from the infotree exporter script, including the kinds of nodes and other metrics.

```
cd scripts/infotree_exporter
uv run infotree_metrics.py
  --root /home/andrew-peterson/code/lean-experiment/infotree_output/Mathlib \
  --out /home/andrew-peterson/code/lean-experiment/infotree_metrics.json
```
