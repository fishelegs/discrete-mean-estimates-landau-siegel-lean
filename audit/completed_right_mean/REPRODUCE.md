# Reproduce the public evidence

Use Python 3.8 or newer, with only its standard library. From this directory:

    python3 check_author.py
    python3 check_independent.py
    python3 verify_bundle.py

The verifier reruns the portable checks and compares their complete JSON outputs against AUTHOR_RERUN.json and INDEPENDENT_RERUN.json. It also checks the file inventory, every file hash and MANIFEST.json against MANIFEST.sha256. No script writes evidence files or calls Lean.

Optionally verify referenced sources and public predecessor evidence:

    python3 verify_bundle.py --repo /path/to/repository

Require independent acceptance before treating the package as accepted source-level evidence:

    python3 verify_bundle.py --require-accepted

This command checks that the recorded final independent decision accepts the stated source-level scope. Hashes establish byte identity, not the truth of an analytic theorem. Original and rerun receipts are separate because historical checks also fingerprinted unpublished locations. Their portable mathematical checks are preserved.

The independent historical run had 13 groups: ten exact mathematical groups, two frozen-input groups, and one source-premise inventory. The portable independent script preserves the ten mathematical groups. The bundle verifier replaces the original location-specific input checks and optionally checks the ten-file SOURCE_SCOPE.json inventory against --repo. INDEPENDENT_ORIGINAL_CURATED.json retains historical mathematical results and source scope while omitting unrelated worktree listings; the original receipt hash remains in PROVENANCE.json.
