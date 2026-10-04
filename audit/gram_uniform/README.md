# Actual fixed-profile uniform arithmetic residual

The six `ZhangLS.Spec.ActualGramUniform*` modules prove that the actual P7
arithmetic residual is `o(alpha)` for two fixed smooth complex-valued profiles.
The headline theorem is
`ZhangLS.Spec.actualGramUniform_smooth_residual_little_o`.

Fix `c > 0` and `f,g : R -> C`, both smooth, with closed support contained in
`[251/500, 201/400]`. For every `epsilon > 0`, the theorem chooses one `N >= 2`
before the modulus `D`, the real primitive character `chi`, and `j : Fin 3`.
For every `D >= N` satisfying the unchanged original
`NormalizedAssumptionA chi`, it bounds the norm of the literal original
strict-box P7 arithmetic sum minus its exact differential main by
`epsilon * lemma44PaperAlpha D`.

The main retains the actual ramified coefficient
`norm(chi(n)) * Lambda(original betas,n,1-beta_j) / phi(n)`, the original strict
indices, the factor `LDerivAtOne(chi)^2 / log(P)^2`, and the exact finite profile
kernel with `f, deriv f, g, deriv g`. No model arithmetic coefficient is
substituted. The genuine arithmetic `Pi(d,r)` remains through the second-side
estimates and is removed only by the existing exact divisor collapse.

The common threshold is proved internally for all four assembly slots: the
actual first norm, first error, second error, and second-main norm. These four
bounds are derived from the accepted integral estimates and fixed profile data.
They are not new arithmetic hypotheses. The active products satisfy the actual
support cutoff, including its boundary. Their harmonic mass is charged only
through the proved support ceiling.

The quantitative bound is
`C_res * (1 + 9 log L)^(k+42) * (log T)^5 * L^(-15)`, where `L=log D`,
`log P=L^9`, `log T=L^(11/10)`, and `k` is the sum of the existing boundary-xi
and Pi exponents. The exact square identity gives
`C_res^2 * (1 + 9 log L)^(2(k+42)) * L^(-19)`; the existing polylogarithmic
comparison gives the claimed `o(alpha)` bound, with `alpha=pi/L^9`.

This proves the residual bridge. It does not evaluate the remaining ramified
main, identify an actual/model Gram form, prove nondegeneracy or strict gain,
or establish the completed fixed-H norm limit `m_H`.

## Evidence

- Six fresh central builds passed on 2026-10-04, using Lean 4.30.0,
  `-j1 -M6144`, the shared serialization lock and existing dependency objects
  read only. The recorded peak RSS was at most 4,629,800 KiB
- The fresh exact central ownership/type/axiom audit passed:
  **133 owned declarations = 38 explicit source declarations + 95 generated**
- Actual owners are obtained with `Environment.getModuleIdxFor?`. All owned
  declarations are included, including structure constructors, projections,
  recursors, equation helpers and generated proof declarations. Owned axioms
  are rejected. Every transitive axiom set is a subset of
  `{propext, Classical.choice, Quot.sound}`
- The executable audit pins every exact owner/name pair, full pretty-type Lean
  hash and universe-parameter list. The public declaration manifests pin the
  full pretty type and raw `Expr` by SHA256, each transitive axiom set, and the
  sorted direct-reference set by SHA256 and count
- Full pretty types and raw expressions are present and untruncated in the
  private audit log. Some full expressions are too large for the public file
  size limit; none is replaced by a shortened type in the audit
- The ordered import union contains 6,969 modules, including 867 repository
  modules. Counts and hashes are pinned; complete module lists remain in the
  private log. This is not a full-project rebuild or a claim that unrelated
  modules have passed fresh verification
- Every central source was byte-compared to its frozen original after only
  qualifying bare `ActualGramUniform*` import lines. `sources.json` records
  both byte hashes and the number of qualified import lines for all six files

The source/type pins serve as the scope regression checks, including the exact
quantifier order, assumptions, complex profiles and actual arithmetic main.
No additional duplicate theorem aliases or endpoint examples are claimed.

`proof-builds.json` records the six successful builds and hashes of their
private object/log/receipt files. `receipt.json` records the fresh pinned audit,
its private full-log hash and dependency inventory hashes. `owners.json` gives
per-module counts. `declarations-01.json` and `declarations-02.json` contain the
compact per-declaration evidence. `SHA256SUMS` covers the exact declared public
file set except itself; it is integrity evidence, not an independent signature.
All public files are UTF-8 and at most 150,000 bytes.

## Verify an existing complete audit log

Run from the repository or unpacked package:

```sh
python3 audit/gram_uniform/verify_evidence.py /absolute/private/Inventory.log \
  --repo-root /absolute/path/to/repository
```

The verifier checks the bounded `audit/gram_uniform` directory's exact file set
and all declared source/audit/file hashes. It permits unrelated files elsewhere
in a complete repository. It also checks the full private log against every
public declaration/type/universe/axiom/reference/import pin. It writes no files
and performs no compilation. `--repo-root` additionally checks the six applied
source files in that checkout.

## Reproduce the audit only

Requires Lean 4.30.0 and existing compiled objects for all six modules and their
dependencies. Supply the complete, already working read-only import path. Lean
chooses namespace prefixes according to that path's order, so use the same
complete central object root/overlay used for the six verified builds before
other roots. This script does not build missing objects or construct an overlay.

```sh
python3 audit/gram_uniform/reproduce_audit.py \
  --repo-root /absolute/path/to/repository \
  --work-dir /absolute/private/fresh-audit-directory \
  --lean /absolute/path/to/lean-4.30.0/bin/lean \
  --lean-path '/absolute/central-objects:/absolute/dependency-objects:...' \
  --lock-file /absolute/shared/private-lean.lock
```

The reproducer validates the published evidence and source hashes, acquires the
shared lock, runs a single `-j1 -M6144` Lean inventory check with no object output,
and verifies the new complete log. It writes only its log and receipt to the
fresh private work directory. It never calls Lake or writes dependency caches.
The existing six successful fresh builds are recorded evidence; this smaller
command reruns the exact type/axiom inventory rather than repeating those builds.
