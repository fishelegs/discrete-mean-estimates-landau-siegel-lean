# Independent MC6 square-nu-tail verification

This records scoped cross-machine verification of exact commit
`3203236c046a128ecaedbefffb41ab1fce539f6d`. It does not certify the full
repository, the source-only analytic completion, the signed gap, or the final
paper theorem. No proof sources were changed by this verification.

`VERIFICATION.json` preserves the observed counts, timing, source and audit
hashes. Both complete audit logs have the same SHA256 as the published cloud
receipt. Duplicate logs and all compiler caches remain outside this commit.

The recorded run rebuilt 129 project modules, including all 16 critical
modules, and reused 115 hash-matched inherited MC6 objects. It completed two
unchanged owner audits, all source checks and 324,079 fresh finite companion
assertions. Wall time was 447.294 seconds; peak compiler RSS was 3.29 GiB.

## Reproduction

Use an exact target checkout with pinned Lean 4.30.0 and the pinned packages'
compiled dependencies already available. Shared inputs are read-only; provide
a new output directory outside them. The script uses Python's standard library
and runs one compiler at a time with `-j1 -M4096`.

```sh
python reproduce.py --repo TARGET_CHECKOUT --packages PINNED_PACKAGES \
  --lean PINNED_LEAN --check-only
python reproduce.py --repo TARGET_CHECKOUT --packages PINNED_PACKAGES \
  --lean PINNED_LEAN --output NEW_PRIVATE_OUTPUT
```

Without `--seed-root`, reproduction freshly compiles the entire **scoped
244-module source closure**, not the repository. With `--seed-root` pointing
to the original MC6 project object cache, the recorded 115 object hashes must
match exactly and the script reproduces the 129-compile schedule. All 16
critical modules are refreshed in either mode. A new machine normally uses the
fresh-closure mode; recorded MC6 timing is not a prediction for that machine.

On a shared MC6 machine, run the whole script through the existing compiler
semaphore wrapper, reserving at most one compiler slot. `--check-only` performs
no compilation and writes no output. The portable script's input checks were
run in both modes; its full compilation workflow was not rerun for this
verification-only commit. The recorded run and audit hashes come from the
completed MC6 validation, not from a new run of the sanitized script.
