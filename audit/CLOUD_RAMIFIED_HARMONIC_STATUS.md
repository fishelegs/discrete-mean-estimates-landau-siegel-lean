# Ramified harmonic finite-arithmetic lemma

This draft adds the actual finite ramified double-sum estimate

    sum (1 <= d,m <= X, D divides d*m)
      norm(upsilon(d)) norm(nu(m)) tau_4(d) tau_4(m) / (d*m)
      <= tau_8(D)/D * H_X^16
      <= tau_8(D)/D * (1 + log X)^16.

The constant is one. The coefficients are the existing convolution-defined
functions of an actual `RealPrimitiveCharacter D`. The capstones are
`ramifiedHead_actual_harmonic_le` and `ramifiedHead_actual_log_le`.
They require a positive conductor and natural cutoff X >= 1. They do not assume
(A), squarefree D, a target estimate or coprimality of either summation index.

## Included proof and audit files

The five `ZhangLS/Spec/RamifiedHeadHarmonic*.lean` modules supply divisor-weight
identities, real-character coefficient bounds, the ramified reindexing, and the
two capstones. The three root `audit/RamifiedHeadHarmonic*.lean` modules contain
endpoint regressions, named axiom checks, and a complete defining-owner audit.
Both generated All files include the five production modules.

The owner inventory checks 56 declarations: 25 explicit production declarations,
9 explicit regression declarations and 22 compiler-generated declarations. It
checks full elaborated types, exact raw-type hashes, universes and the allowed
axiom set. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The
inventory includes generated equations owned by downstream modules.

Regressions cover an actual conductor-one character, an empty X=1 range for D>1,
overlap at conductors 8 and 12, zero coefficients and zero-index exclusion, and
the non-coprime retained tuple (D,d,m)=(12,18,4). The conductor-8 source comment
uses the phrase "prime-square"; its theorem is the stated prime-power endpoint.

## Validation scope

An independent semantic review accepted the finite mathematical statement.
Central verification freshly compiled three published prerequisites, the five
production modules and the three audits with Lean 4.30.0, one compiler thread
and a 4096 MiB limit. Portable reproduction and 21 integrity checks passed.
All 243 project dependency-source pins were rechecked against the draft base.
No unpublished external proof dependency is required.

The submitted eight Lean files retain the exact verified bytes. An additional
bounded compilation on the exact draft overlay at base `da1eed4` passed on
2026-10-04: all 11 targets compiled freshly, generated imports and audit ordering
passed, and the complete owner/type/axiom output matched the frozen verifier.
The fresh inventory output SHA256 is
`622758a38cf8305b775b97ad293c5619ef6974ab805cff9faef60c2af54b1236`.
These checks do not claim a fresh rebuild of the entire repository. The PR's
normal hosted workflow checks all project modules and root audit files.

Reproduction in a checkout with the pinned toolchain and dependencies:

    python3 tools/generate_spec_all_imports.py --check
    python3 tools/generate_all_imports.py --check
    lake build
    lake env python3 tools/verify_audit_modules.py

## Mathematical boundary

This completes the finite arithmetic lemma only. Its analytic attachment to the
original head operator, the logarithmic integration budget and the D-decay
corollary are separate results. This PR does not prove a bad-family estimate,
the unresolved strict signed upper bound or the original main conclusion.
The original-paper ledger remains 40/51 (37 original statements and 3 repairs).
