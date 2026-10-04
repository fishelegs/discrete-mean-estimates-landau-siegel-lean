# MC6 three-bridge central audit

**PASS:** all 14 proof modules have fresh successful Lean 4.30.0 builds; all five original audit files compile, including all 37 regression examples. A second, pinned audit independently checks exactly 242 defining-module-owned declarations: 130 Abel, 65 fixed-profile, and 47 diagonal. Of these, 138 are explicit source declarations and 104 are generated declarations.

The 19 input files match the exported manifest for commit `9a2f00e69b5bbb48a71b1ee8ad738c93ebc66798` byte for byte and match the applied cloud checkout. The export commit identifier is supplied by that manifest; this package does not claim that the applied checkout's HEAD is that commit. The central proof build receipts predate this ownership audit and were checked against all 14 exact source SHA256s and private output objects. A separate full run of the portable reproducer also passed all 14 builds, five original audits, and the pinned inventory after checking its dependency overlay and repository installation behavior.

## What is checked

- All constants whose actual defining module is one of the 14 selected proof modules are selected using `Environment.getModuleIdxFor?` and `env.header.moduleNames`
- The complete discovered module/name list is pinned and checked in both directions, including generated equation, simplifier, and proof declarations
- Explicit declarations are independently enumerated from the 14 source files, with source lines recorded
- Every owned axiom declaration is rejected; every transitive axiom dependency must belong to `Classical.choice`, `Quot.sound`, or `propext`
- Every declaration's full `pp.all` type, raw `Expr` type, universes, and direct references are emitted to the private log; no pretty type contains an omission marker
- The pinned Lean audit verifies all type rendering fingerprints and universe lists; the Python verifier independently checks SHA256s of both full type representations
- All 6,175 imported modules, including 248 repository modules, are listed in exact order; direct references are retained for all 242 declarations

Ownership is never inferred from namespace prefixes. For example, `CoprimeProfileAbel.mainConstant.eq_1` is owned by `CoprimeProfileAbelEuler`, while the original definition is owned by `CoprimeProfileAbelSummatory`. The diagonal-generated `lemma83PaperBeta.eq_1` is included by its actual owner.

The original regression breakdown is arithmetic 8, Abel profile 8, diagonal 6, fixed profile 15. `FixedHDiagonalAxioms.lean` is the fifth audit file and contains no regression examples. Its separate 47-owner audit also passes.

## Files

- `../MC6ThreeBridgesInventory.lean`: compact exact owner, name, type, and universe pins, plus the active transitive axiom audit
- `receipt.json`, `proof-builds.json`, `regressions.json`: sanitized execution evidence
- `sources.json`, `export-manifest.json`: the exact original 19 inputs
- `owners.json`, `declarations-*.json`: complete owner counts, names, source classification, type SHA256s, universes, and axiom sets
- `direct-references-*.json`: complete direct constant-reference lists
- `loaded-modules-*.txt`, `repository-loaded-modules.txt`: exact dependency inventories
- `verify_evidence.py`: check the published package and a complete private inventory log
- `reproduce.py`: rebuild into a separate private output directory and rerun all checks
- `SHA256SUMS`: integrity hashes of every other file in this package, relative to the package root; these hashes are not an independent signature

All public files are UTF-8 text, each smaller than 150,000 bytes. The complete 2.9 MB type log is deliberately private; its digest is in the receipt. No public receipt contains a local execution path.

## Reproduce

Use Lean `leanprover/lean4:v4.30.0`, the exact 19 repository inputs, and the repository's existing dependency objects. No dependency download or `lake` command is used. The base `LEAN_PATH` must contain the existing package, mathlib, repository, and toolchain object directories. The new private proof object directory is prepended automatically. Because Lean resolves an entire project prefix from its first search-path root, unchanged project dependency objects are linked read-only into that directory in base-path order. Every output stem and suffix for the 14 fresh modules is reserved; the reproducer rejects any such output that is a symlink.

Run from the package root:

```sh
python3 audit/three_bridges/reproduce.py \
  --repo-root REPOSITORY \
  --work-dir PRIVATE_OUTPUT_OUTSIDE_REPOSITORY \
  --lean LEAN_EXECUTABLE \
  --base-lean-path EXISTING_READ_ONLY_LEAN_PATH \
  --lock-file SHARED_LEAN_LOCK
```

Every compiler process uses `-j1` and acquires the supplied shared exclusive lock. Each proof and original audit uses `-M4096`; the combined inventory uses the approved `-M6144`. The initial combined discovery exceeded the 4096 MB heap before producing rows. Both the discovery and the pinned audit passed at 6144 MB. Their actual peak resident set was approximately 4.1 GiB. No larger heap or concurrent Lean process was used.

For a completed full inventory log:

```sh
python3 audit/three_bridges/verify_evidence.py PRIVATE_INVENTORY_LOG --repo-root REPOSITORY
```

The verifier checks the exact declared manifest paths and the complete bounded `audit/three_bridges` directory, while allowing unrelated files elsewhere in an installed repository. It checks all published SHA256s, exact declarations, full pretty and raw type hashes, universes, transitive axioms, direct references, complete dependency order, and source hashes. Its recorded build/regression checks verify the receipts. `reproduce.py` performs fresh compilations to regenerate that evidence.

## Scope

This is kernel, type, ownership, and regression evidence for these three bridges. It does not establish a final norm bound, a gain theorem, final target closure, or the separate source-level semantic review. Passing the standard-axiom check does not remove explicit mathematical hypotheses from any theorem; the full types and original sources remain the authority.
