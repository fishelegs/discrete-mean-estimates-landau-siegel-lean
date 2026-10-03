# Reproduce the public evidence

The author checker uses the Python standard library. The independent checker also uses SymPy and SciPy. The full package was tested with Python 3.12.14, SymPy 1.14.0 and SciPy 1.17.0; the two library versions are pinned in requirements.txt.

From this directory, after installing the listed requirements in your Python environment:

    python3 check_author.py
    python3 check_independent.py
    python3 verify_bundle.py --require-accepted

The verifier reruns both portable scripts and compares their JSON outputs against AUTHOR_RERUN.json and INDEPENDENT_RERUN.json. Exact results are compared literally. The raw floating-point Fourier error may vary across platforms; both recorded and newly measured values must be nonnegative and at most 5e-10. Each numerical identity also has its original per-case tolerance check inside the independent script. This supports normalization bookkeeping, not uniform analytic certification.

The verifier checks the file inventory, every file hash, and MANIFEST.json against MANIFEST.sha256. No script writes evidence files or calls Lean. Optionally verify the referenced repository sources and public predecessor evidence:

    python3 verify_bundle.py --require-accepted --repo /path/to/repository

The historical independent run had 25 groups: 23 mathematical/numerical groups and two frozen-input groups. The portable checker preserves all 23 mathematical/numerical groups, while the bundle verifier separately checks the public evidence. Original and rerun receipts are distinct. Historical source hashes establish provenance; they are not the current hashes of curated public proofs.

Analytic acceptance is the full independent mathematical argument, particularly its Sections 6–8. Neither finite checks nor hashes certify a signed constant, an exceptional-character instance or a Lean theorem.
