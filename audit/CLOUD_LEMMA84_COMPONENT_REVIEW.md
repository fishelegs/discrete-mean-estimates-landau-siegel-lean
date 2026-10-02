# Independent semantic review of frozen Lemma 8.4 component

Decision: ACCEPT AS COMPONENT, not as completion of original Lemma84Target.
Review date: 2026-10-02. Reviewer: independent Section 8 weighted-budget worker.

Scope reviewed: original TeX 2392–2417; frozen Lemma84Definitions,
Lemma84Residue, Lemma84ArithmeticCircle, Lemma84CircleBudget,
Lemma84SumCirclePolynomial, Lemma84Repaired; frozen manifest and axiom report.
All 44 source entries in FULL-MANIFEST.json (33 own and 11 prerequisite entries)
were independently SHA256-checked during this review; no mismatches.
Central integration is separately responsible for the fresh full rebuild.

1. Actual-object agreement. lemma84XiSum is the positive strict n<x sum with
   χ(n) times the genuine Section 7 lemma83Xi, denominator n, (x/n)^(-βμ),
   and log(x/n). The n=x logarithmic endpoint is exactly zero. The original
   cyclic β shifts and fixed c′ are retained. lemma84MainTerm has the displayed
   G signs and coefficients, including −(βj+1−βμ)(βj+2−βμ)log(x)/βμ.
   The residue identity proves this expression from the actual rational
   two-pole integrand, rather than postulating its residue.
2. Π is precisely lemma83Pi from the accepted Section 7/8.3 definitions, with
   both prime products and the possible q=2 zero. The circle is the normalized
   positively oriented radius-5α circle, using the actual shifted L quotient
   and proved Euler correction. Its radius has not been silently changed.
3. Contour repair is explicitly separated: Perron may start at any positive
   real part; the proved transfer uses 6α so the 5α disk lies inside the
   rectangle. The final actual-sum-to-circle theorem has only the original
   (A), positive d,r, dr<PT^-2, T<x<P and fixed positive c′ hypotheses. It does
   not assume a contour estimate, zero oracle, reciprocal bound, or convergence
   assertion. These obligations are discharged by its proved prerequisites.
4. Quantifier audit. For each fixed positive c′, the conductor threshold is
   selected before D, χ, j, μ, d,r,x. All local smallness, L lower bounds and
   absorption thresholds are included there. The repaired error constant 3 is
   chosen even before c′. The capstones use all natural μ because their definition
   selects β6 when μ=6 and β7 otherwise; the repaired original-format target
   explicitly restricts μ=6 or 7. This benign strengthening does not introduce
   another smoothing parameter.
5. No hidden premise in the L^-5 branch. The actual error is bounded by the
   sum of L^-6 transfer, C1 L^-6 ||Π|| Taylor contribution and C2 L^-7 polylog
   correction. The proved uniform Π polylog estimate and elementary eventual
   absorption give ≤3 L^-5. No D-varying quantity is absorbed as a constant.
6. No hidden premise in the Π=0 branch. Its extra premise is explicitly Π=0;
   it removes the main term and Taylor term by multiplication by zero, without
   division by Π. The remaining two errors are ≤2 L^-6. The concrete χ(2)=1,
   2|d, 2∤r regression correctly witnesses this potentially vanishing factor.
7. Original exponent is not certified. Lemma84Target remains the unchanged
   additive uniform L^-6 assertion. The component does not prove it. The
   unresolved C1||Π|| L^-6 term is displayed, not renamed or hidden. The local
   Taylor input is completed Lemma5.8, not the unavailable literal full 5.6.
8. Frozen FULL-AXIOMS.json reports only propext, Classical.choice and Quot.sound.
   No sorryAx or other custom axiom is reported. This semantic review does not
   replace the central fresh-build and axiom-extraction audit.

The downstream Section 8 cutoff layers, exact weighted asymptotic, (8.10),
λ approximation and passage to (8.11) are outside this component's claim.
Their unfinished status does not invalidate the proved quantitative component,
but this review does not certify preservation of the final paper conclusion.
