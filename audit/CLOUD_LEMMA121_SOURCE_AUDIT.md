**Historical source audit:** the low/transition unfinished-status comments below are superseded by CLOUD_LEMMA121_CONCRETE_SCOPE.md. Original alpha1 and printed high-phase issues remain.

# Original Lemma 12.1 source audit

Source: Zhang, arXiv:2211.02515v1, PDF p.68; supplied official TeX at `/tmp/zhang-2211.02515-source.tex`.
Source SHA256: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.
PDF SHA256: `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`.
Exact excerpts with original line numbers are frozen in `source-excerpts.txt`.

## Frozen definitions and statement

- L=log D; P=exp(L^9); alpha=pi/log P; t0=L^519; T=exp(L^(11/10)).
- One shared fixed positive c′ enters all three shifts (2.13): beta1=i alpha(1−5c′ alpha L), beta2=2i alpha(1+c′ alpha L), beta3=3i alpha(1−c′ alpha L).
- beta6=3i alpha/2, from (2.22).
- P1=P^(63/125)=P^0.504; P2=P^(1/2) T^(−10), from (2.21).
- A=P''1=P^(62/125) D t0=P^0.496 D t0; B=P''2=P^(1/2) D t0.
- kappa13(n)=(log P1)^(−1)(n/A)^(−beta6) log(n/A) for A<n<B, and zero otherwise. Both support endpoints are strictly excluded; the upper endpoint does not have zero logarithm.
- Actual sum S_j(d)=sum_l chi(l) kappa13(dl)/l^(1−beta_j), over positive integers. `lemma121Sum` uses the exact finite strict upper cutoff and actual RealPrimitiveCharacter evaluation.
- Low branch: d<=A/T gives S_j(d)<<T^(−kappa), an absolute positive exponent and constant chosen before c′.
- Transition: A/T<d<=A gives S_j(d)<<alpha1. The supplied TeX repeatedly uses alpha1 but contains no definition of that symbol. The full target therefore explicitly exposes alphaOne as an unresolved parameter; it is not silently equated with L^(−7).
- High branch: A<d<P2 gives S_j(d)=(L′(1,chi)/log P1)(−1+(2 beta6−beta_j)log(d/A)+epsilon), with strict |epsilon|<10^(−5).

`Lemma121PrintedTarget` freezes all branches/ranges; `Lemma121PrintedHighTarget` separately freezes the high branch. Neither proposition is asserted as a theorem.

## Verified source-level obstruction

Set h=log(d/A). The exact phase in the printed proof is

  E(b,a,h)=exp(−b h)(−1+(b−a)h), b=beta6, a=beta_j.

The printed last step replaces this with −1+(2b−a)h, while retaining a normalized error below 10^(−5). This is an error *inside* the factor L′(1,chi)/log P1; it is not an absolute unnormalized 10^(−5) error.

`lemma121_limiting_phase_exceeds_printed_budget` proves, in Lean, that at the internal scaled point h/log P=1/500 and limiting j=3 shift a=3i pi, b=3i pi/2,

  |E(b,a,1/500)−(−1+(2b−a)/500)| > 1/100000.

Writing u=3pi/1000, the real-part magnitude is cos u+u sin u−1. The proof uses 3<pi<=4, 1−u²/2<=cos u, and u−u³/4<sin u; it is rational inequality checking, not floating-point evidence.

Important logical limit: this audits the phase linearization used in the proof. It is **not** an actual character counterexample to the original conditional theorem. In particular, no existence of large characters satisfying (A) is asserted, and possible eventual impossibility of (A) is not ignored.

## Primary checked replacement

`lemma121_exact_high_proved : Lemma121ExactHighTarget` proves the actual sum estimate on the *entire original high range*, keeping the exact phase:

  S_j(d) = (L′(1,chi)/log P1) E(beta6,beta_j,log(d/A)) + O(L^(−15)).

The absolute O constant is 20+2*lemma82LocalErrorConstant, chosen before c′; only the modulus threshold depends on c′. The theorem even allows real d, hence includes the original natural d. It uses actual Abel tails and actual local L-function Taylor bounds. The strict unweighted endpoint correction is explicitly proved and bounded by 1/x; it is never dropped.

This exact-phase version is the preferred deliverable for downstream use. It avoids assuming any tolerance that the printed linearization cannot support.

## Optional numerical replacement, expressly changed

`lemma121_repaired_high_proved : Lemma121RepairedHighTarget` keeps the original linear phase but replaces |epsilon|<10^(−5) with |epsilon|<10^(−3).

- Actual phase error <=101/125000=0.000808 uniformly in the original high range and all three actual shifts.
- Actual analytic error after normalization <=0.0001 at a sufficiently large modulus, using the independently proved original Lemma 5.7 derivative lower bound.
- Their sum is strictly below 0.001.

This is a deliberately weaker **alternative high-branch conclusion**, not the printed theorem. No claim is made that enlarging this error by 100 preserves later numerical inequalities. Those uses must be separately audited or recomputed with the exact phase.

## Status and remaining work

Original Lemma 12.1 is NOT complete. Both low branches remain to be proved. The meaning of alpha1 remains unresolved in the supplied source. The high branch has a faithful exact-phase replacement and an explicitly labelled 10^(−3) alternative; the printed 10^(−5) high target is unproved.

No sorry, admit, custom axiom, or result-shaped analytic assumption is introduced. Auxiliary lemmas accept explicit elementary geometric or algebraic hypotheses; all such hypotheses are discharged in the checked capstones. All 42 public declarations in the frozen high-stage modules have axiom audit output restricted to propext, Classical.choice, and Quot.sound. Twenty semantic regressions are kernel checked.
