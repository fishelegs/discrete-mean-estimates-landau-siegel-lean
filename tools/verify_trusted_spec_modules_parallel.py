#!/usr/bin/env python3
"""Check every Spec source with the Lean kernel, using bounded parallelism."""

from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    os.chdir(root)
    try:
        jobs = int(os.environ.get("ZHANGMATH_SPEC_JOBS", "4"))
    except ValueError:
        print("ERROR: ZHANGMATH_SPEC_JOBS must be an integer", file=sys.stderr)
        return 2
    if not 1 <= jobs <= 16:
        print("ERROR: ZHANGMATH_SPEC_JOBS must be between 1 and 16", file=sys.stderr)
        return 2

    logs = root / "audit/spec_kernel_logs"
    logs.mkdir(parents=True, exist_ok=True)
    summary = root / "audit/spec_kernel_modules.txt"
    summary.write_text("")
    modules = sorted(p for p in (root / "ZhangLS/Spec").glob("*.lean")
                     if p.name != "All.lean")

    # Compile the dependency graph before starting concurrent, read-only checks.
    # Every source is then independently elaborated and kernel-checked by Lean.
    built = subprocess.run(["lake", "build", "+ZhangLS.Spec.All:olean"])
    if built.returncode:
        summary.write_text("trusted_spec_modules=FAIL\n"
                           "reason=Spec dependency build failed\n")
        return 1

    def check(source: Path) -> tuple[str, bool]:
        relative = source.relative_to(root).as_posix()
        log = logs / f"{source.stem}.log"
        with log.open("w") as output:
            try:
                checked = subprocess.run(["lake", "env", "lean", relative],
                                         stdout=output, stderr=subprocess.STDOUT)
                success = checked.returncode == 0
            except OSError as error:
                output.write(f"ERROR: could not execute Lean: {error}\n")
                success = False
        return relative, success

    results: dict[str, bool] = {}
    print(f"Checking {len(modules)} Spec modules with {jobs} workers", flush=True)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        pending = [executor.submit(check, source) for source in modules]
        with summary.open("a") as progress:
            for future in as_completed(pending):
                relative, success = future.result()
                results[relative] = success
                status = "PASS" if success else "FAIL"
                progress.write(f"{status}\t{relative}\n")
                progress.flush()
                print(f"{status}\t{relative}", flush=True)
                if not success:
                    print((logs / f"{Path(relative).stem}.log").read_text(),
                          file=sys.stderr, flush=True)

    failures = sorted(name for name, success in results.items() if not success)
    passed = sum(results.values())
    lines = [f"{'PASS' if success else 'FAIL'}\t{name}"
             for name, success in sorted(results.items())]
    lines += [f"trusted_spec_modules={'FAIL' if failures else 'PASS'}",
              f"trusted_spec_modules_passed={passed}",
              f"trusted_spec_modules_total={len(modules)}",
              f"trusted_spec_workers={jobs}"]
    if failures:
        lines.append(f"first_failed_spec_module={failures[0]}")
    summary.write_text("\n".join(lines) + "\n")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
