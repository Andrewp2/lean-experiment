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
    parser.add_argument("--log-file")
    parser.add_argument("--memory-max", default="16G")
    parser.add_argument("--no-systemd", action="store_true")
    parser.add_argument("--systemd-system", action="store_true")
    args = parser.parse_args()

    if args.batch_size <= 0:
        raise SystemExit("--batch-size must be > 0")

    if args.total is None and not args.to_end:
        raise SystemExit("Provide --total or pass --to-end")

    if args.total is not None and args.total <= 0:
        raise SystemExit("--total must be > 0")

    if args.total is None and args.to_end:
        mathlib_dir = os.path.join(args.root, "Mathlib")
        if not os.path.isdir(mathlib_dir):
            raise SystemExit(f"Expected Mathlib directory at {mathlib_dir}")
        total_files = 0
        for root_dir, _dirs, files in os.walk(mathlib_dir):
            for name in files:
                if name.endswith(".lean"):
                    total_files += 1
        remaining = total_files - args.start
        if remaining <= 0:
            raise SystemExit("--start is out of range for Mathlib files")
        args.total = remaining

    script_dir = os.path.dirname(os.path.abspath(__file__))
    end = args.start + args.total
    for batch_start in range(args.start, end, args.batch_size):
        remaining = end - batch_start
        limit = min(args.batch_size, remaining)
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
        exit_code = run_and_tee(cmd, script_dir, args.log_file)
        if exit_code != 0:
            print(f"[infotree_export] batch failed with exit code {exit_code}", file=sys.stderr)
            return exit_code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
