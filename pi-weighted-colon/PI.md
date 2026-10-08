# Unconditional pointwise Hermite nonvanishing at 2*pi*i

This checkpoint supplies the pi-transcendence input through the separately
attributed, approved A7 proof and proves nonvanishing of the **actual** Hermite
coefficient matrix at `2 * (Real.pi : ℂ) * Complex.I`, for every natural N and
every equivalence reindexing its original columns. It provides no quantitative
lower bound or badly-approximable theorem.

## Exact theorem and input

`src/PiHermiteNonvanishing.lean` imports the unchanged evaluation bridge and the
six-file upstream capstone. Its final theorem has no transcendence premise:

```lean
theorem complexHermiteCoefficientMatrix_det_ne_zero_two_pi_I (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) :
    (squareComplexHermiteCoefficientMatrix N e
      (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0
```

`hermite_determinant_aeval_ne_zero_pi` gives the actual determinant-polynomial
evaluation form, and `canonicalComplexHermiteCoefficientMatrix_det_ne_zero_pi`
gives the canonical original-column ordering. The input theorem is precisely
`LeanFormalizations.Transcendence.transcendental_pi_axiomClean :
Transcendental ℚ Real.pi`, not an assumed replacement for it. The existing
`piHermiteParameter_transcendental_iff` transports it to the exact complex
parameter, then the already proved determinant evaluation theorem applies.

## A7 provenance and compatibility

Only these six project modules are vendored under `vendor/gotrevor-pi/src/`:
`ETranscendental`, `PiLindemann`, `HermiteLindemann`, `MonicRootSums`,
`SubsetSumEsymm`, and `PiTranscendental`, all in the original
`LeanFormalizations.NumberTheory.Transcendence` module path.

- Upstream: https://github.com/gotrevor/lean-formalizations
- Exact commit: `bad0e21a37874f09f45072dad6225de55742e6c5`
- Author/copyright: Trevor Morris, 2026; original file headers retained.
- Apache License 2.0: exact upstream `vendor/gotrevor-pi/LICENSE`, plus attribution
  in `NOTICE` and exact file SHA-256 values in `provenance.json`.
- Original upstream toolchain is 4.31.0. The referenced public CI
  https://github.com/gotrevor/lean-formalizations/actions/runs/37548551487
  was checked as successful at that exact commit.
- **No compatibility edits** were required: all six ported SHA-256 values equal
  the originals. No additional upstream project is imported; all other imports
  are Mathlib at our existing 4.30 pin.

The six files include 36 named declarations. `A7ImportedAudit.lean` checks each
declaration's actual signature and recursively prints its axioms, including the
capstone. This covers all imported project helpers, even the included e-related
helpers which are not the final pi headline. No project source has `sorry`,
`admit`, a custom axiom, `native_decide`, `unsafe`, or execution hooks.

## Verification and reproduction

The cumulative verifier compiles 49 positive modules and requires 22 expected
failures, for 71 checks, and audits all 492 named declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. Warnings are errors. New
regressions check the literal real-pi input, literal `2*pi*i` parameter, all N
and original-column reindexings, the canonical ordering, scale zero, and an
actual nonconstant matrix entry at pi. Expected failures reject an incorrect
pi entry and substituting `4*i` for the pi parameter.

On KEYISHEN-MC6 the verified cache is an independent copy of the existing
pinned project, filled with the same revision's official Mathlib cache. Its
source/dependency revisions are checked before compilation; the earlier cache,
proof outputs, global settings and isolated W2 receipts are preserved.

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-08/task/pi-a7-mathlib-project \
  --out /tmp/pi-a7-replay
```

Replay makes no network request, invokes no Lake hooks and installs nothing.
It compiles serially with one worker. Existing modules retain a 4096 MiB limit;
the vendor and modules importing its broad Mathlib environment use 8192 MiB.
An initial 4096 MiB `MonicRootSums` attempt aborted with a Lean interpreter
memory exception. Before the bounded retry, the host reported 48 GiB physical
RAM and a 41% memory-free percentage. The successful raw-source port required
no proof changes. Exact replay commands, exits, source/cache/output/log hashes,
and all axiom sets are recorded in `verification/replay-receipt.json`.

The pinned Mathlib itself still does not export a pi-transcendence theorem;
the historical library-gap record and its name-rejection test remain accurate.
The separately audited A7 source supplies the missing input for this checkpoint.
This work does not rerun or incorporate the separate W2 proof.

## Remaining scope

This is pointwise nonvanishing of the actual Hermite coefficient matrix. It
does not formalize the derivative-jet parameter factor, Schur-compressed
residual identity or a residual/analytic bridge, and gives no uniform
archimedean bound, effective constants, or pi badly-approximability conclusion.
