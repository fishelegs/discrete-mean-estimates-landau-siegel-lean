# Reproduce and verify

Requirements: Python 3.9 or later, mpmath 1.3.0, and SymPy 1.14.0. The recorded run used Python 3.12.14. The pinned packages are in [requirements.txt](requirements.txt). In a suitable Python environment, install them with `python -m pip install -r requirements.txt` if needed.

From this directory, run:

    python run_checks.py

The runner also works when invoked by its relative or absolute location from another working directory. It resolves all files against its own directory, performs no downloads, edits no files, and invokes no Lean process. It first verifies the complete SHA256 manifest, checks local Markdown links and disallowed machine-specific references, requires both numerical packages, and then runs the two original scripts separately. Each output must exactly match its bundled expected text.

To verify integrity and document links without running the mathematical scripts:

    python run_checks.py --verify-only

Individual mathematical scripts can also be run directly:

    python checks/check_algebra.py
    python checks/check_independent.py

The author's script alone can skip its gamma check when mpmath is absent. The full runner requires mpmath and rejects an output mismatch, so it never silently accepts that reduced coverage.

Saved outputs:

- [Algebra output](results/algebra.txt): exact rational moment/precision/support budgets, 2,688 finite root/parity/Gauss identities, 600 pointwise Gram/target/norm/compensation checks, and exact gamma/CRT quotient checks
- [Independent output](results/independent.txt): exact rational exponent budgets, 1,500 finite divisor-majorant checks, 1,620 root/Gauss identities including nonsquarefree conductors, symbolic Gram conjugations, inherited-branch sign regression, gamma parity quotients, and six numerical Gaussian Mellin checks
- [Runner output](results/runner.txt): successful end-to-end run, also reproduced after relocating the bundle

These are finite numerical/symbolic regressions. They do not prove uniform analytic estimates, evaluate the main arithmetic sums, establish a favorable sign, discharge C₁/T₁ completion/tails/shifts, or provide Lean verification. A matching hash proves byte integrity relative to this manifest, not the correctness of the mathematics.
