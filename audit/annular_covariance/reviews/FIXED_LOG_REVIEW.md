# Independent review: fixed logarithmic support windows

Date: 2026-10-03. Separate extension audit; no Lean, repository edits, or formalization. The previously reviewed [dyadic report](../reports/DYADIC_REPORT.md) (accepted source hash before path normalization) is frozen at SHA256 `1839df7636ee4adcdacae99228c5ecf4b089556815fcc6c17d5b0888e3a91ea2` and is not being silently rewritten or broadened.

## Final verdict

The wider support class passes the independent tail and moment calculations and the completed primary addendum passes review. Endpoint integral bounds avoid any loss proportional to the ratio of the two support endpoints. The C1 right completion still costs O(a^-1 L^-200), while C1 left and both T1 sides still cost O(a^-1 L^-14). The fixed logarithmic widths admit nonzero profiles with fixed coefficient bounds and fixed profile L2 norms. This does not by itself give an actual zero-measure Gram lower bound or a favorable target pairing.

Accepted primary addendum: [fixed-log addendum](../reports/FIXED_LOG_ADDENDUM.md) (accepted source hash before path normalization), SHA256 `c457ac0dfb91b14a9bd45dee4615fa489cb98c2a90c0569d00a8ca3e0873c52e`. I checked the full file, reran its `check_fixed_log_windows.py` successfully, and reverified the frozen base-report hash. The primary addendum makes no profile nondegeneracy or actual zero-energy claim; section 4 below supplies the precise optional profile-norm comparison and its chi-density qualification. No correction remains requested for this extension.

## 1. Exactly what changes, and what stays fixed

For this addendum only, bounded coefficients independent of p and psi have supports

    A: [P^.502,P^.504],
    B: [P^.499,P^.5],
    J: [P^.5,P^.504].

Use C1 kappa cutoffs R=P^.9995 on the right and V=P^1.005 on the left. For T1 use P^1.005 on both sides. The original J1 remains the literal source target: its triangular coefficient profile has support [.5,.504] in u=log n/log P and maximum 1. A is contained in that target coefficient class, so T1[A,A] and T1[A_i,A_j] are included as before.

All exact residue, gamma branch, conductor/parity, primitive-character kernel, right-minus-left, and unit-restriction definitions remain those of the frozen report. Assumption (A), its exponent 2022, the requested corresponding exponent 2024, and all original P/t0/window/family exponents remain fixed. This is an extension to a different explicitly quantified trial class, not a claim about dropping parts of the original broad H1/H2.

## 2. Uniform interval sums and the absence of a hidden real-part cost

Write A_-=P^.502, A_+=P^.504, B_-=P^.499, B_+=P^.5, J_-=P^.5, J_+=P^.504. Uniformly in the full outward-shift range, the following elementary estimates hold with absolute constants:

    sigma>=3/2: sum_{n>=X} n^-sigma <= 3 X^(1-sigma),
    sigma<=-1/2: sum_{n<=X} n^-sigma <= X^(1-sigma),
    sigma>=3/2: sum_{n<=X} n^(sigma-1) <= X^sigma,
    sigma<=-1/2: sum_{n>=X} n^(sigma-1) <= 3 X^sigma.

For the two infinite sums, compare the first term plus the integral; the denominators sigma-1 and -sigma are bounded below by 1/2. For the two finite sums, number of terms times the largest term suffices. Integer rounding is harmless because X is exponentially larger than the maximum real-part shift L^9; alternatively use the first-term-plus-integral inequalities with the exact integer endpoints. The constants do not grow with sigma.

Thus on the right use the lower endpoints for A(s), B(s); on the left use the upper endpoints. Counting A_+ terms and assigning every term the value A_-^-sigma would create an unnecessary growing prefactor. That argument is not used. No factor (A_+/A_-)^|sigma| or (B_+/B_-)^|sigma| is introduced.

Put q_t=p(t/2pi), Q_t=D p^2(t/2pi)^2 as in the base review. The exact gamma estimates and bounded B_beta/E_chi factors are unchanged.

### C1 right

For sigma>=3/2 the tail integrand without omega is bounded by fixed log factors times

    Q_t^.5 [Q_t/(R A_- B_-)]^(sigma-1).

Here R A_- B_-=P^2.0005, so the unsimplified power gap is .0005. The exact extra D t0^2 factor is P^o(1); eventually the bracket is at most P^-.00025. Shifting the tail to sigma=.5+L^9 gives exp(-cL^18). On the horizontal pieces the displayed bound decreases with sigma, so its near-endpoint exp(O(L^9)) envelope is dominated by the original Gaussian exp(-L^10/4).

### C1 left

For sigma<=-1/2 the tail is bounded by fixed log factors times

    A_+ B_+ D^-.5 [D V/(A_+ B_+)]^sigma.

Now A_+B_+=P^1.004, so V/(A_+B_+)=P^.001; the D factor helps. The bracket is at least P^.0005 eventually. The same leftward shift to sigma=.5-L^9 is valid and negligible. No missing inverse-gamma or conductor factor is supplied by a stationary-point heuristic.

### T1 right and left

With R_T=V_T=P^1.005, the right tail is bounded by fixed log factors times

    R_T A_- q_t^-.5 [q_t J_+/(R_T A_-)]^sigma,

whose bracket has power exponent 1+.504-1.005-.502=-.003 before t0. The left tail is bounded by fixed log factors times

    A_+ q_t^.5 [V_T J_-/(q_t A_+)]^sigma,

whose bracket has power exponent 1.005+.5-1-.504=.001 before division by t0. Both have fixed positive slack in the appropriate direction. They absorb the original t0 rather than freezing it away. The same finite-window tail/horizontal proof applies.

For reference, the already mentioned C0[J,B] extension with cutoff P^1.005 on both sides has right/left gaps .004/.001. Its unit-modulus roots do not change the completion estimate. This is still not an evaluation of its main term.

## 3. Moments, exceptional completion, and the actual contour

The base proof's positive multiplicative majorant eta=|kappa|*|kappa| handles the hard-truncated fourth moment without restoring complex cancellation. The wider supports do not alter its Euler estimates. The relevant polynomial-length exponents are now

    C1 right kappa square: 1.999 < 2,
    C1 left/T1 kappa polynomial: 1.005 < 2,
    A cube and J cube: 1.512 < 2,
    B cube: 1.5 < 2.

Hence source Lemma 3.3 still supplies kappa fourth/second costs L^144/L^36 and all sixth-moment costs L^81. The exact unchanged Holder budgets are

    144/4+81/6+81/6-739(5/12)+77(7/12)=-200,
    36/2+81/6+81/6-739/6+77(5/6)=-14.

The larger support counts on the bounded real-part strips only change an exp(O(L^9)) horizontal envelope, which the source Gaussian already dominates. All reciprocal-L contour moves remain restricted to the good family; bad-family inward shifts contain only finite truncated polynomials. Both actual vertical contributions are retained with their original R-L orientation. The high upper-half-plane B_beta branch, absence of crossed poles, and exp(O(L^9 log L)) good-family reciprocal-L envelope are unchanged.

All m,n remain below p, and p>D. The right cutoff P^.9995 is below p. The longer left/T1 cutoffs and every restored infinite sum must still exclude p|ell; the base arithmetic formulas explicitly do so. No unit Gauss/Kloosterman expression is evaluated at a zero argument.

Thus the same exact finite-window arithmetic representations extend to this wider class, with total normalized error O_C(a^-1 L^-14) and the separate C1 right error O_C(a^-1 L^-200). Constants depend on fixed coefficient bounds and the fixed finite trial count, not on D or sigma. Fixed linear combinations stay in scope without growing coefficient maxima.

## 4. What fixed profile norms do and do not establish

For a fixed nonzero piecewise C1 profile f supported on [u_-,u_+] and coefficients a_P(n)=f(log n/log P), elementary summation gives

    (log P)^-1 sum_n |a_P(n)|^2/n
       = integral_{u_-}^{u_+}|f(u)|^2 du + o(1).

The logarithmic widths here are fixed: .002 for A, .001 for B, .004 for J. By contrast a dyadic interval [P^u,2P^u] has logarithmic width log 2/log P=O(L^-9). Normalizing a fixed bounded profile on a fixed logarithmic window therefore requires only a fixed coefficient multiplier; it does not force a sqrt(log P) factor as a shrinking dyadic profile would in this coefficient norm.

Concrete bounded examples are triangles of height 1 on the three intervals. Their exact profile L2 squared norms are 1/1500 for A, 1/3000 for B, and 1/750 for the original J triangle. Multipliers sqrt(1500) and sqrt(3000), if desired for unit A/B profile norms, are fixed constants compatible with a fixed uniform coefficient bound.

If the coefficients instead contain chi(n), the ordinary harmonic norm has the density factor phi(D)/D:

    (log P)^-1 sum_n |chi(n)f(log n/log P)|^2/n
       = (phi(D)/D) integral |f(u)|^2 du + o(1).

For these piecewise smooth fixed profiles this follows by averaging the periodic coprimality indicator over blocks of length D; the error is exponentially negligible since the lower endpoint is P^u with fixed u>0 whereas D=P^o(1). The factor cannot be silently omitted or called a uniform positive constant as D varies. The underlying unmasked profile integral nevertheless remains fixed. General merely bounded coefficient sequences can vanish and have no automatic norm lower bound.

Most importantly, these statements concern coefficient/profile norms. The actual positive zero-measure quantities H(A,A), H(B,B), cross correlations, and any Gram residual norm still require their arithmetic calculation. Fixed profile width prevents one particular mistaken normalization inference; it does not supply the signed gain, eliminate all near-null directions, or validate division by an uncomputed residual norm. The original target and the original quantitative stopping condition remain unchanged.

## Checks and frozen-file control

Run [the independent fixed-window check](../scripts/check_fixed_log_windows.py); its output is [the independent fixed-window results](../results/FIXED_LOG_INDEPENDENT_ORIGINAL.txt). It verifies all six support gaps, large-sieve lengths, exact Holder budgets, target inclusion, fixed triangular profile norms, the chi-square density, and that the frozen base report hash has not changed. These checks complement the analytic interval-sum proof above.

The primary addendum's independently rerun checks also pass the exact widths/gaps/lengths/budgets and 36 finite endpoint-bound regressions. Neither suite evaluates an arithmetic main term or proves a signed gain. No original frozen report, original review, or original check file was modified by this separate extension audit.
