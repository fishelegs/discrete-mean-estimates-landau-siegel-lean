# Explicit error scales and source-repair ledger

The intended goal remains the paper's final mathematical conclusion. Evidence-based repairs of ambiguous notation and proof steps are permitted, but every repaired statement must be distinguished from the printed statement. No original result is added to the completion count here.

## Verified quantitative interfaces

The six theorems in `ZhangLS/Spec/PaperErrorScaleBudget.lean` use the actual definitions L=logD, P=exp(L^9), T=exp(L^(11/10)), and alpha=pi/logP. They prove:

1. logT/logP = L^(-79/10)
2. alpha logT = pi L^(-79/10)
3. logT/logP <= L^-7 when L>=1
4. alpha = pi L^-9
5. If an actual complex error e satisfies norm(e)<=C alpha, the already-proved actual L-function derivative bound gives norm(L'(1,chi)^2 e) <=(16 exp1)^2 C pi L^-5
6. If norm(e)<=C logT/logP and C>=0, the same derivative bound gives norm(L'(1,chi)^2 e)<=(16 exp1)^2 C L^-3

The latter two use genuine `LDerivAtOne`, not an arbitrary substitute. They assume the stated error bound; they do **not** prove it or count any unfinished15.2/15.3 conclusion. They do not assume(A). Three regressions expand the actual P/T/alpha definitions. No symbol called alpha-one is introduced.

## All source uses mapped

The [28-occurrence index](cloud_alpha1_occurrences.json) records the exact lines of the official TeX and the proof obligation attached to each use. Categories are: phases (4), finite divisor Euler products (2), cutoff boundaries (4),15.1 (1), large-prime coefficients (2),15.2 (1),15.3/local factors (3), Section15 smoothing/residues (3), Section16 Euler ratios (2), AppendixB residues/cutoffs (6).

The cutoff width L^-7.9 explains why assigning L^-8 indiscriminately is unsafe. L^-7 is a possible loose envelope for several displayed calculations, but is not asserted to be a complete reconstruction of the undefined notation. A universal envelope can lose necessary information:16.1 explicitly asks for L^-8, while other locations have logT/logP effects. The approach is therefore to preserve named, proved quantitative errors until each downstream multiplication or sum has been checked.

## Exact propagation gaps requiring further proofs

- Section15 equation(15.22) explicitly has an O(L^-1) remainder. The following(15.23) displays O(L^-3). The former alone does not imply the latter. A sharper earlier bound or an explicitly repaired intermediate rate is needed
- In the reduction to(16.14), Lemma15.1's O(alpha-one tau2(n1)) error is replaced by O(D^-c). The cited lemma alone does not supply this exponential improvement; divisor weights and aggregate error must be retained
- AppendixA's proof of16.1 ends with O(alpha-one), but16.1 states O(L^-8). This needs the actual sharper local-factor calculation; it cannot be justified by an arbitrary shared symbol
- The Section15 residue factors are displayed as constants+O(L^-1), then multiplied by the actual a. The available general bound for a is O(L^4), so that coarse displayed rate alone is insufficient to conclude absolute o(1). Retaining sharper phase/shift rates or checking a relative-error formulation is necessary
- The15.3 branch is checking whether the exact prime coefficient requires removal of L(s−beta_j,chi)^2 rather than the printed L(s,chi)^2. This is under active local-identity verification, not a declared counterexample. If a shift repair is confirmed, its actual Mellin residues must be recomputed; the proved alpha logT scale is potentially useful

These observations identify missing implications in the displayed estimates, not proofs that the final theorem is false. A revised proof may establish stronger underlying bounds or show a weaker intermediate estimate still suffices for the unchanged final conclusion. Neither possibility is assumed.

## Separate final obligations

The original literal5.6 modulus-one branch is still not used circularly. Its proved nonprincipal port can be used only after each consumer's conductor/nonprincipal conditions are checked. The effectivity of final constants also remains a separate formal obligation; ordinary classical existence is not an effective extraction certificate.

## Verification of the six budget interfaces

Lean4.30.0, Linux x86_64, 2026-10-02: six theorem interfaces use only standard axioms; three expanded regressions pass without warnings; all4920 project build jobs pass; coverage668/933 and placeholder/structure checks pass for1030 Lean sources. The strict heuristic audit retains361 candidates and nonzero exit, with no new candidate from this module. See [regressions](CloudErrorScaleRegression.lean), [axiom output](cloud_error_scale_axioms.log), and [hashes/verification](cloud_error_scale_verification.json). This verifies the budget implications only, not the estimates listed as pending above.
