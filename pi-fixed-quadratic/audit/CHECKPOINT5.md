# Actual log-minor arithmetic checkpoint — 2026-10-09 UTC

Partial formalization. The fixed-real-quadratic-field pi finiteness theorem is
still not exported or claimed. This checkpoint closes changed arithmetic
connections rather than adding an assumed integrality interface.

## Actual polynomial and exact denominator

`truncatedLog T` is `PowerSeries.trunc T (PowerSeries.log Complex)`.
`logDenominator T` is exactly `Nat.lcmUpto (T-1)` (empty value 1).
`formalEntry_truncatedLog_cleared_gaussian` proves actual entry clearing by
product L_i^(alpha_i-b_i). `formal_minor_truncatedLog_cleared_gaussian`
instantiates the generic determinant clearing theorem; there is no abstract
entry-membership premise. `exists_gaussian_cleared_minor` constructs P over
Gaussian integers with map(P)=Q*D and degrees <= e_i, where
`e_i=sum selected columns alpha_i-sum rows b_i`. Cancellation may lower the
actual degree. Incompatible products are discarded before natural subtraction.

## Complete polynomial coefficient envelope

The l1 seminorm is the sum of absolute values of polynomial coefficients.
Its sum/product/power rules and factorial determinant bound are proved.
For nested time polynomials, `timeCoefficientL1` also weights time coefficient s
by (1/2)^s. Finite convolution proves submultiplicativity; the finite geometric
sum gives a uniform truncated-log bound 2. Thus the actual entry envelope is

    binomial product * 2^s * (3/2)^h * (2k+2)^(sum_i(alpha_i-b_i)).

This is a deliberately coarser constant than the paper's log 2 / C_k. It is
independent of every T_i and introduces no log-log height term. It proves the
needed coefficient control directly; no new analytic or completeness axiom is
introduced. The actual whole determinant envelope is

    M! * 2^(sum rows s) * (3/2)^(sum columns h)
       * 2^(sum columns |alpha|) * (2k+2)^(sum_i e_i).

The cleared polynomial's envelope contains exactly one additional Q factor.

## Same-field arithmetic connection

`quadratic_multi_l1_mahler_lower` derives the multivariate, compatible
simultaneous-conjugation bound from the proved degree-two Gaussian norm.
It uses one coefficient-l1 cost and a_i^e_i, independent of the coordinate count.
There is no Cartesian nonvanishing assumption.

`formal_minor_fixed_field_arithmetic` applies it to the actual P just constructed
and its actual coefficient envelope. Its exact type concludes

    product R_i^e_i <= Q^2 * (displayed factorial envelope)
                           * product M_i^e_i * norm(D(x)).

Its hypotheses explicitly include a degree-two Galois tower over the fraction
field of Gaussian integers, a compatible complex embedding, primitive integer
root-pair factorizations, nonzero leading coefficients and the actual minor's
nonzero target value. Gaussian norm integrality, descent, the coefficient
bound, and degrees are conclusions/proofs, not assumptions. Constructing this
tower from the requested fixed real field and its canonical minpolys remains.

## Verification

Ordinary isolated Lean 4.34.1 replay: **38 compiler checks, 148 declaration
(type and axiom) audits**, including **13 diagnostic-matched expected failures**.
All own declarations use only propext, Classical.choice, Quot.sound. No
sorry/admit, project axiom, native_decide, unsafe code or proof hooks occur.

Positive regressions include T=0/1 empty lcm, actual truncation T=3,
clearing -1/2 to -1, coefficient-l1=1 of that cleared entry, T=100 uniform bound,
and the T=1 center entry envelope. A new expected failure rejects dropping
its log denominator; the prior binomial, coefficient-cost, Cartesian, relative
field degree, primitivity, degree-equality and nonexistent final pi checks remain.
Static placeholder/structure scans pass on 2197 Lean files. The 274 protected
old files and original clean branch at cae0ad9 are unchanged.

Checkpoint 4 standalone and old pi aggregate CI success were downloaded and
matched to local source/axiom hashes and path-normalized logs (31/84, 93/622).
The independent full root kernel run is followed separately to terminal status;
unfinished runs are not counted as passing.

## Exact actual upstream packet bridge

The separately compiled `UpstreamFormalEntryBridge` now audits five declarations.
It proves exact specialization to a selected square minor of upstream's actual
`Row`/`Column` packet and transports genuine minor nonvanishing. With legal
selected columns and a nonzero formal minor, it proves

    sum_i w_i e_i <= card(Row)*H - sum_rows sum_i w_i b_i.

No p/q input or independent per-coordinate replacement enters that budget.
The bridge adds one compiler invocation and five declaration audits beyond the
38/148 standalone checks. The six upstream interface/axiom audits are freshly
compiled, and all prior 872 upstream source/log/olean checks are revalidated.
These bridge checks are local cross-project checks, not the standalone CI.
The prior checkpoint's single-entry bridge receipt has been replaced by this
stronger receipt; `audit_entry_bridge.py` reproduces all five declarations.

## Remaining work

Construct the actual fixed field/minpoly/height tower; derive the normalized
arithmetic errors and factorial remainder limit; genuinely generalize upstream
proved geometric surjectivity and analytic packet/parameter theorems; select
successively unbounded height approximants; finish the finiteness contradiction.
The paper's sharper lcm constant has not been proved here; the available formal
constant log 4+4 remains available. No varying-field, BA or degree-exact lower
exponent conclusion is asserted.
