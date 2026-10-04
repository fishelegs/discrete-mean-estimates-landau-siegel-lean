# Actual Gram profile audit checkpoint

Focused validation passed for 16 owner modules: **154 owned declarations and 92 source-public declarations**. The six restored integral/profile modules contribute **44 owned / 29 source-public**, including 15 generated helpers. These are the existing checkpoint counts, not newly proved theorem counts.

The final executable audit pins all 154 exact owner/name pairs and every universe parameter list, checks the complete rendered type of each declaration using Lean's deterministic 64-bit String hash, prints both full rendered and raw expression types, and rejects transitive axioms outside `propext`, `Classical.choice`, and `Quot.sound`. The 64-bit type fingerprints have collision risk. `declarations.json` additionally records SHA256 for every complete type rendering and raw expression representation from the successful final run. A separate fresh run checked all 154 rendered types by exact full-string equality; its sanitized receipt and source/log hashes are included.

Run the audit from the repository root:

```sh
lake env lean -j1 -M6144 audit/CloudGramProfileInventory.lean
```

The standalone Python verifier can compare a new audit log with all published per-declaration SHA256s and the exact module list:

```sh
python audit/gram_profile/verify_audit_output.py fresh-audit.log
```

`sources.json` records the sixteen inventoried source SHA256s, direct imports and declaration counts. All six restored source hashes, import-only remaps, object hashes and trace hashes match the independent accepted review. `loaded-modules-01.txt` and `loaded-modules-02.txt` list the exact 6,964 imported modules; `repository-loaded-modules.txt` lists its 862 repository modules. These are dependency provenance lists, not a whole-project rebuild or a semantic review of all dependencies. The six module build receipts remain the earlier fresh 6/6 PASS evidence; they are not relabeled as new builds.

The accepted mathematics covers moving-boundary integration, actual first-profile norms and first/second-profile errors, smooth-profile traces and bounds, exact finite-box attachment, and supported weighted residual assembly. The second interior term remains the repaired `3 L^(-5)` estimate. The exact main retains the plus Volterra term, original beta shifts, genuine Pi, character/totient coefficients and literal `L'(1,chi)^2/B^2` prefactor.

Weighted assembly still has four explicit inputs: actual first norm, actual first error, actual second error, and second main norm. A common uniform substitution and its arithmetic/profile conditions remain open. This checkpoint does not establish the actual fixed-H norm, actual/model Gram identity, Gram nondegeneracy, phase complement, target projection or strict gain.
