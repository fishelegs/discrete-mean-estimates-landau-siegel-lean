#!/usr/bin/env python3
"""Reproduce only the pinned square-nu-tail scope; shared inputs are read-only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
RECORD = json.loads((HERE / "VERIFICATION.json").read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(command, cwd):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path, help="checkout at the exact verified commit")
    parser.add_argument("--packages", required=True, type=Path, help="read-only pinned Lake packages directory")
    parser.add_argument("--lean", default="lean", help="pinned Lean executable")
    parser.add_argument("--seed-root", type=Path, help="optional exact recorded MC6 project object cache")
    parser.add_argument("--output", type=Path, help="new private directory for objects, logs and receipts")
    parser.add_argument("--check-only", action="store_true", help="validate inputs without compiling or writing")
    args = parser.parse_args()
    repo, packages = args.repo.resolve(), args.packages.resolve()
    lean = shutil.which(args.lean)
    if not lean:
        raise ValueError("Lean executable unavailable")
    assert checked(["git", "rev-parse", "HEAD"], repo) == RECORD["target_commit"]
    version = checked([lean, "--version"], repo)
    assert "version 4.30.0" in version and RECORD["lean_commit"] in version
    assert checked(["git", "rev-parse", "HEAD"], packages / "mathlib") == RECORD["mathlib_commit"]
    pin_file = repo / "audit/square_nu_tail/PROJECT_SOURCE_PINS.json"
    assert digest(pin_file) == RECORD["source_pin_manifest_sha256"]
    pins = json.loads(pin_file.read_text())
    assert len(pins) == 244

    def check_sources():
        for module, item in pins.items():
            assert digest(repo / item["path"]) == item["sha256"], module
        assert digest(repo / "audit/CloudSquareNuTailCentralAudit.lean") == RECORD["audit_source_sha256"]

    check_sources()
    visited, order = set(), []

    def visit(module):
        if not module.startswith("ZhangLS.") or module in visited:
            return
        visited.add(module)
        for dependency in pins[module]["imports"]:
            visit(dependency)
        order.append(module)

    visit("ZhangLS.Spec.SquareNuTailConvolutionCapstone")
    assert visited == set(pins)
    critical = set(RECORD["fresh_critical_modules"])
    seeds = RECORD["seed_olean_sha256"] if args.seed_root else {}
    assert not critical.intersection(seeds)
    seed_root = args.seed_root.resolve() if args.seed_root else None
    for module, expected in seeds.items():
        assert digest(seed_root / (module.replace(".", "/") + ".olean")) == expected, module
    stdlib = Path(checked([lean, "--print-prefix"], repo)) / "lib/lean"
    dependencies = [p / ".lake/build/lib/lean" for p in packages.iterdir() if p.is_dir()] + [stdlib]
    loaded = set()
    for part in (1, 2):
        loaded.update((repo / f"audit/square_nu_tail/IMPORTED_MODULES_{part}.txt").read_text().splitlines())
    assert len(loaded) == 5998
    assert hashlib.sha256(("\n".join(sorted(loaded)) + "\n").encode()).hexdigest() == RECORD["loaded_modules_sha256"]
    external = loaded - visited
    assert len(external) == 5754
    for module in external:
        relative = module.replace(".", "/") + ".olean"
        assert any((root / relative).is_file() for root in dependencies), module
    queue = [module for module in order if module not in seeds]
    assert len(queue) == (129 if seeds else 244)
    if args.check_only:
        print(json.dumps({"status": "INPUTS_VALID", "target_commit": RECORD["target_commit"],
                          "project_closure": 244, "planned_fresh_compiles": len(queue),
                          "critical_refreshes": 16, "external_cache_modules": 5754}))
        return
    if args.output is None:
        parser.error("--output is required for compilation")
    output = args.output.resolve()
    assert not output.exists(), "Use a new private output directory"
    for protected in (repo, packages, seed_root):
        if protected is not None:
            assert not output.is_relative_to(protected), "Output must be outside shared inputs"
    output.mkdir(parents=True)
    private, logs = output / "lib/lean", output / "logs"
    logs.mkdir()
    for module in seeds:
        source = seed_root / (module.replace(".", "/") + ".olean")
        target = private / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        for companion in source.parent.glob(source.name + "*"):
            shutil.copy2(companion, target.parent / companion.name)
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(map(str, [private] + dependencies))
    results, begin = [], time.monotonic()

    def run(label, command, filename):
        log, start = logs / filename, time.monotonic()
        with log.open("w") as stream:
            process = subprocess.Popen(command, cwd=repo, env=environment,
                                       stdout=stream, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        row = {"label": label, "exit_code": process.returncode,
               "seconds": round(time.monotonic() - start, 3),
               "max_rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
               "log_sha256": digest(log), "log_bytes": log.stat().st_size}
        results.append(row)
        (output / "RESULTS.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(row), flush=True)
        if process.returncode:
            raise RuntimeError(f"{label} failed; inspect its private log")

    for module in queue:
        source = repo / pins[module]["path"]
        target = private / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        run(module, [lean, "-j1", "-M4096", "-R", str(repo), "-o", str(target), str(source)], module + ".log")
    audit_target = private / "audit/CloudSquareNuTailCentralAudit.olean"
    audit_target.parent.mkdir(parents=True, exist_ok=True)
    for number in (1, 2):
        name = f"audit-pass-{number}.log"
        run(f"AUDIT {number}", [lean, "-j1", "-M4096", "-R", str(repo), "-o", str(audit_target),
                               str(repo / "audit/CloudSquareNuTailCentralAudit.lean")], name)
        run(f"AUDIT_CHECKER {number}", [sys.executable, "audit/square_nu_tail/check_audit.py", str(logs / name)],
            f"audit-checker-{number}.log")
    first, second = [(logs / f"audit-pass-{n}.log").read_text() for n in (1, 2)]
    blocks = lambda text: sorted(s.rstrip() for s in re.findall(
        r"^OWNED_TYPE .*?(?=^(?:DECL_REF |OWNER |LOADED_MODULE |OWNERSHIP_PASS )|\Z)", text, re.M | re.S))
    assert len(blocks(first)) == 182 and blocks(first) == blocks(second)
    marker = "OWNERSHIP_PASS PROOF 155 PUBLIC 100 TEST 27"
    assert first.split(marker, 1)[1].strip() == second.split(marker, 1)[1].strip()
    run("PACKAGE", [sys.executable, "audit/square_nu_tail/verify_package.py"], "package.log")
    run("SOURCE_COMPANION", [sys.executable, "-I", "audit/square_factor_tail/verify_bundle.py",
                             "--repo-root", ".", "--rerun"], "source-companion.log")
    check_sources()
    for module, expected in seeds.items():
        assert digest(seed_root / (module.replace(".", "/") + ".olean")) == expected, module
    receipt = {"status": "PASS_SCOPED", "target_commit": RECORD["target_commit"],
               "fresh_project_compiles": len(queue), "project_source_pins": 244,
               "audit_passes": 2, "owned_declarations": 182, "wall_seconds": round(time.monotonic() - begin, 3),
               "audit_log_sha256": [digest(logs / f"audit-pass-{n}.log") for n in (1, 2)],
               "full_repository_validation": False}
    (output / "SUMMARY.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
