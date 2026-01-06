#!/usr/bin/env python3
import argparse
import os
import subprocess
import sys


def run_and_tee(cmd, cwd, log_file):
    if log_file:
        log_handle = open(log_file, "a", encoding="utf-8")
    else:
        log_handle = None
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        for line in proc.stdout:
            sys.stdout.write(line)
            sys.stdout.flush()
            if log_handle:
                log_handle.write(line)
                log_handle.flush()
        return proc.wait()
    finally:
        if log_handle:
            log_handle.close()


def iter_mathlib_files(mathlib_dir):
    collected = []
    for root_dir, dirs, files in os.walk(mathlib_dir):
        dirs.sort()
        files.sort()
        for name in files:
            if name.endswith(".lean"):
                collected.append(os.path.join(root_dir, name))
    collected.sort()
    return collected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--total", type=int)
    parser.add_argument("--to-end", action="store_true")
    parser.add_argument("--batch-size", type=int, default=5)
    parser.add_argument("--max-seconds", type=int)
    parser.add_argument("--rss-log-mb", type=int)
    parser.add_argument("--max-rss-mb", type=int)
    parser.add_argument("--mem-debug", action="store_true")
    parser.add_argument("--continue", dest="continue_flag", action="store_true")
    parser.add_argument("--full-infotree", action="store_true")
    parser.add_argument("--gzip", action="store_true")
    parser.add_argument("--skip-on-error", action="store_true")
    parser.add_argument("--max-infotree-nodes", type=int)
    parser.add_argument("--log-file")
    parser.add_argument("--memory-max", default="16G")
    parser.add_argument("--no-systemd", action="store_true")
    parser.add_argument("--systemd-system", action="store_true")
    args = parser.parse_args()

    def log(message, *, stderr=False):
        stream = sys.stderr if stderr else sys.stdout
        stream.write(f"{message}\n")
        stream.flush()
        if args.log_file:
            with open(args.log_file, "a", encoding="utf-8") as handle:
                handle.write(f"{message}\n")

    if args.batch_size <= 0:
        raise SystemExit("--batch-size must be > 0")

    if args.total is None and not args.to_end:
        raise SystemExit("Provide --total or pass --to-end")

    if args.total is not None and args.total <= 0:
        raise SystemExit("--total must be > 0")

    mathlib_files = None
    if args.total is None and args.to_end:
        mathlib_dir = os.path.join(args.root, "Mathlib")
        if not os.path.isdir(mathlib_dir):
            raise SystemExit(f"Expected Mathlib directory at {mathlib_dir}")
        total_files = len(iter_mathlib_files(mathlib_dir))
        remaining = total_files - args.start
        if remaining <= 0:
            raise SystemExit("--start is out of range for Mathlib files")
        args.total = remaining
    if args.continue_flag:
        mathlib_dir = os.path.join(args.root, "Mathlib")
        if not os.path.isdir(mathlib_dir):
            raise SystemExit(f"Expected Mathlib directory at {mathlib_dir}")
        mathlib_files = iter_mathlib_files(mathlib_dir)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    end = args.start + args.total
    for batch_start in range(args.start, end, args.batch_size):
        remaining = end - batch_start
        limit = min(args.batch_size, remaining)
        if args.continue_flag:
            batch_end = batch_start + limit
            slice_files = mathlib_files[batch_start:batch_end]
            if slice_files:
                all_done = True
                for path in slice_files:
                    rel = os.path.relpath(path, args.root)
                    base, _ext = os.path.splitext(rel)
                    out_name = base + (".json.gz" if args.gzip else ".json")
                    out_path = os.path.join(args.out, out_name)
                    if not os.path.exists(out_path):
                        all_done = False
                        break
                if all_done:
                    log(f"[infotree_export] continue skip batch {batch_start}..{batch_end}")
                    continue
        if args.no_systemd:
            cmd = [
                "lake",
                "exe",
                "infotree_export",
                "--root",
                args.root,
                "--out",
                args.out,
                "--start",
                str(batch_start),
                "--limit",
                str(limit),
            ]
        else:
            cmd = [
                "systemd-run",
                "--scope",
            ]
            if not args.systemd_system:
                cmd.append("--user")
            cmd += [
                "-p",
                f"MemoryMax={args.memory_max}",
                "lake",
                "exe",
                "infotree_export",
                "--root",
                args.root,
                "--out",
                args.out,
                "--start",
                str(batch_start),
                "--limit",
                str(limit),
            ]
        if args.max_seconds is not None:
            cmd += ["--max-seconds", str(args.max_seconds)]
        if args.rss_log_mb is not None:
            cmd += ["--rss-log-mb", str(args.rss_log_mb)]
        if args.max_rss_mb is not None:
            cmd += ["--max-rss-mb", str(args.max_rss_mb)]
        if args.mem_debug:
            cmd.append("--mem-debug")
        if args.continue_flag:
            cmd.append("--continue")
        if args.full_infotree:
            cmd.append("--full-infotree")
        if args.gzip:
            cmd.append("--gzip")
        if args.max_infotree_nodes is not None:
            cmd += ["--max-infotree-nodes", str(args.max_infotree_nodes)]
        if args.skip_on_error:
            cmd.append("--skip-on-error")
        log(f"[infotree_export] batch start {batch_start}..{batch_start + limit}")
        log(f"[infotree_export] batch cmd: {' '.join(cmd)}")
        exit_code = run_and_tee(cmd, script_dir, args.log_file)
        if exit_code != 0:
            log(f"[infotree_export] batch failed with exit code {exit_code}", stderr=True)
            return exit_code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
