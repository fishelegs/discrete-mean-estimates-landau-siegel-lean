# CI closeout: completed 2026-10-09 UTC

The independent full-target Linux replay and every requested existing root CI
have completed successfully. This closeout changes only evidence and reports;
it adds no mathematical or formalization work.

The full-target source/script/workflow commit is
`d261f45e66f49df4eb4eec8f895cb8855bc484d1`. Its independent
[Linux run 37905909230](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37905909230)
has all 908 receipt entries verified: 843 upstream and 63 local positive
compilations, two expected failures, and six exact actual type/axiom audits.
Only `propext`, `Classical.choice`, `Quot.sound` occur. All source and uploaded
log hashes match the reviewed closure. The final actual theorem type matches
CP11. The elapsed compiler sum is 3945.879 seconds. Only the exact mathlib
package cache was reused; every OAI/local artifact was newly compiled.

The evidence was first pushed in
`adee9588e1d3dca8c962d5a01874fe2d10c29e85`. Subsequent changes are evidence and
README only; proof sources, pins, replay code and workflow remain unchanged
from the independently verified replay commit.

## Existing root CI terminal results

Each run below used the original Lean 4.30.0 and passed all 1565 trusted Spec
modules individually, the Spec aggregate, full project build, audit regressions,
and Gaussian closure. Every uploaded individual log and aggregate report was
checked. The same 1565 modules were rechecked across runs; these are not distinct
module counts to be added together. The root proof sources remain unchanged.

| Checkpoint | Commit | Root run | Result |
|---|---|---|---|
| CP6 | `258e210bd7372ef9dc738690a1e01b4f47280632` | [37892853078](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37892853078) | success, artifacts verified |
| CP7 | `eab794cb9682580399c88b53a958825b435e9cca` | [37895704203](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37895704203) | success, artifacts verified |
| CP8 | `5f84f3ab5f645185e37566025a07c8d31afb7e99` | [37896844472](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37896844472) | success, artifacts verified |
| CP9 | `75cd502b9ba414d5040a6bd7d9e69950e9b2df48` | [37901252348](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37901252348) | success, artifacts verified |
| CP10 | `c3f76706b10f2f1c58101d3fedaa656178b07ac9` | [37902549764](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37902549764) | success, artifacts verified |
| CP11 | `096c4606f31f6817580f62b40dbfdb51c44a7c47` | [37903934463](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37903934463) | success, artifacts verified |
| CP12 | `9bd2f696017f49ca0175721525d43b14474c7d07` | [37905342084](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37905342084) | success, artifacts verified |

The separate CP11 and CP12 arithmetic workflows passed 50 compiler checks and
265 declaration type/axiom audits; their original-pi aggregate workflows passed
93 checks and 622 declaration audits. Their source, type/axiom and normalized
log comparisons passed, as recorded in the adjacent validation receipts.

## Preserved failure and project scope

The first full-target attempt, run `37905342242` at commit
`9bd2f696017f49ca0175721525d43b14474c7d07`, passed eight modules and failed at
`FiniteCoverCohomology` with a memory exception at the initial 6144 MiB limit.
`fresh-linux-initial-memory-failure-receipt.json` and its companion `.log`
preserve this failed attempt. It is never counted as success evidence. The
corrected single-worker 8192 MiB replay completed on the fresh Linux runner.

All 274 protected old-project hashes were rechecked in both checkouts. The
original branch remains clean at `cae0ad9b2069acf3c8814b31af36a1842519ce9e`.
No old 4.30 pins or verified A7/W2/sqrt(2)/Log-Pade proofs changed. The theorem
scope remains the established fixed-real-quadratic upper finiteness statement;
there is no added proof scope, K1--K3, varying-field or BA/non-BA claim. No merge,
PR, package publication or website change occurred. There are no remaining
execution or CI blockers.

`ci-completion.json` records the final verified data and source preservation
checks. This evidence-only closeout skips redundant push-triggered CI; it does
not replace or alter any recorded compiler run.
