# Source and boundary semantic review

This is a source-alignment review of the proved package, separate from kernel regression checking. It is not a claim of an external human or independent-agent review.

## Frozen source

The source is arXiv:2211.02515v1, original TeX lines 2789–2851 (Lemma 10.2), followed by lines 2903–2966 for S_j(a11,a13). Lemma102Definitions.lean was hashed before proof. That frozen hash remains unchanged.

- Actual summand: χ(n) ξ₀ⱼ(n;d,r) times the original tent at log(drn)/log P, divided by n.
- Actual β/c′: lemma83PaperBeta with the same cyclic Fin 3 indexing as the proved Section 7/8 definitions.
- Actual Π: lemma83Pi, including possible zero factors. No division by Π occurs.
- Breakpoints: 0.5=1/2, 0.502=251/500, 0.504=63/125, exactly.
- Interior endpoints: dr≤P^0.5/T; P^0.5<dr≤P^0.502/T; P^0.502<dr≤P^0.504/T.
- Transition bands: (P^0.5/T,P^0.5], (P^0.502/T,P^0.502], (P^0.504/T,P^0.504).

## Frequency and residue

The Section 8 helper `lemma84SmoothingBeta D μ` chooses β7 whenever μ≠6, so μ=0 is not an unshifted value. The new Perron theorem explicitly passes the complex number 0 to the generic, proved pure-imaginary logarithmic kernel. FullRegression includes a check that Nat μ=0 remains β7.

The true L quotient has its actual simple exceptional-zero pole and the logarithmic kernel has a double pole at zero. The contour proof removes these genuine distinct poles. Only after a proved L/Π approximation does the model have a third-order origin pole. Its value is proved with the Cauchy second derivative formula, not imported as a presumed G limit.

## Main-term signs and normalization

The exact tent bridge is 500/log P times the logarithmic second difference at exponents 63/125, 251/500 and 1/2. The residue polynomial is 1+(a+b)log x+ab(log x)^2/2. The three separate algebra lemmas verify:

- Three active cutoffs give L′Π ab log P/500.
- Two active cutoffs give 500L′Π(-1+Y1)/log P.
- One active cutoff gives 500L′Π(1+Y2)/log P.

The original tent and actual ξ appear in the final theorem, not a replacement F/G model. The finite sum equals the literal all-n sum; n=0 and the included top endpoint contribute zero.

## Endpoint handling

The analytic transfer was strengthened to x≥T by directly proving the closed logarithmic exponential bound. Thus dr=P^a/T is not lost between interior and boundary arguments.

The source boundary has strict lower endpoints and two inclusive upper endpoints. `lemma102TransitionPairs` uses exactly that predicate. Its mass proof bounds these original bands by closed [Q/T,Q] bands and then by [Q/T,QT), using T² as thickness. This safely includes dr=Q and does not require the three bands to be disjoint. Their union is bounded by the sum of three actual arithmetic masses. At dr=P^0.504 the original tent vanishes and the finite outer support excludes the endpoint, consistently with the source Ioo last band.

`lemma102FullMain` assigns the first knot to the initial formula and the second knot to the lower formula. Both knots lie in the retained boundary set, where the full actual-sum-minus-selected-main difference is bounded. There is no assumption of agreement of adjacent main formulas at a knot.

## Weighted scope

`lemma102MixedSource` expands the κ₁+ι₂κ₂ first factor using `lemma84Section8FirstSource`, the actual original arithmetic weight `lemma84Section8Weight`, and the literal all-n tent-ξ sum. Equality with the normalized implementation is proved by `lemma102_mixed_source_exact` and checked in the standalone regression.

The interior mass is a genuine harmonic bound for |μ|, |χ|, λ and φ. The boundary mass is a genuine three-layer harmonic estimate. The first inner factor retains its actual κ coefficients and uses an already-proved global bound. No desired weighted estimate is a premise.

The final little-o capstone proves only full ξ-factor replacement in this actual mixed sum. Further first-factor asymptotics, arithmetic summation, phase evaluation, other shifted-tent terms, and Proposition 2.4/MixedMoment mean asymptotics remain outside this theorem. Original pointwise Lemma 10.2 is still open; no impossibility witness is asserted.

## Central source check

The original TeX statements at2789–2851 and the literal mixed-sum display at2903–2966 were reread during central integration. The three ranges and main-term signs, actual companion kappa1+iota2*kappa2, lambda/mu/chi/phi weights, and the distinct zero-frequency Perron convention agree with the exposed source definitions. Closed knot choices in the replacement main term are covered by the proved original boundary-band error; no equality of adjacent formulas at a knot is assumed. Full regression and all 28 modules were freshly built against the central repository.
