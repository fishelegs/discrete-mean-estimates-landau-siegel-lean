# Migration Step 29 — Gaussian tail and cubic summability closure

This step advances the trusted `ZhangLS/Spec` reconstruction through the remaining
Gaussian-tail summability obligation used by Lemma 5.7.

## Lean source changes

`ZhangLS/Spec/Lemma57GaussianGlobal.lean` now contains:

- a split of the positive Gaussian half-line into a finite interval plus a tail;
- an exact tail representation of `zhangGaussianWeight` for nonpositive endpoints;
- the generic bound
  `∫_{y}^{∞} exp(-t^2) ≤ exp(-K*y)/K` for `0 < K ≤ y`;
- the identity for the reflected endpoint along `D^4/n`;
- proof that this reflected endpoint tends to `+∞`;
- an eventual exponential majorant for the sampled Zhang weight.

`ZhangLS/Spec/Lemma57SmoothedSummability.lean` now contains source-level proofs of:

- `zhangGaussianCubicDecay_proved`;
- `lemma57FullSmoothedSummable_proved`;
- `lemma57_full_gaussian_arithmetic_scale_proved`.

The cubic bound uses `K = 3 / (log D)^15`, giving a fixed `D`-dependent constant
multiple of `n^(-3 : ℝ)`.

## Verification status

Static project gates pass:

- trusted Spec umbrella coverage: 19 modules;
- full-project umbrella coverage: 97 submodules;
- 101 Lean source files scanned;
- no code-level `sorry` or `admit`;
- structural checker: 0 failures;
- semantic legacy audit: 38 pre-existing high-risk findings, no new trusted-Spec finding.

The authoritative Lean kernel gate is **not passed in this sandbox** because the
`lean` and `lake` executables are unavailable.  `tools/verify_all_lean.sh` therefore
correctly reports `LEAN_KERNEL_VERIFICATION=FAIL` with all kernel phases `NOT_RUN`.
The theorem terms added in this step must be treated as awaiting Lean 4.30.0 kernel
compilation, not as kernel-verified results.

> Subsequent status: Step 30 compiled this complete theorem chain successfully
> with Lean 4.30.0.  See `MIGRATION_STEP_30.md` for the kernel and CI results.
