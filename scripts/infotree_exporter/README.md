# Infotree exporter script

This is a script that exports Infotrees from mathlib. It has a python script to do batch processing,
which also limits the memory taken by each file which helps stability.

## Run

```
python3 scripts/infotree_exporter/run_batches.py \
  --root /home/andrew-peterson/code/mathlib4 \
  --out /home/andrew-peterson/code/lean-experiment/infotree_output \
  --start 0 --to-end --batch-size 1 \
  --gzip --skip-on-error --continue  \
  --rss-log-mb 10000 --mem-debug \
  --log-file /home/andrew-peterson/code/lean-experiment/infotree_export.txt
```
