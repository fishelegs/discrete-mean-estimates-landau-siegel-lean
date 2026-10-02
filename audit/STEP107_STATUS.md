# Step 107 — Actual cumulative Mangoldt cancellation and smoothing error

The complete original `Lemma56Target` remains **in progress**. The full
ledger remains **17/51 complete, 1 in progress, 33 unstarted**. This step
promotes fifteen trusted modules and **55 proved interfaces**, preserving
the original strict prime window and the faithful principal boundary.

## Actual cumulative arithmetic cancellation

Set U=(log D)^(9/2), B=exp(3U/2), H=exp(2U)/2 and P=exp((log D)^9).
Under the original (A), one threshold chosen before all D, characters,
x and tau gives, for each distinct nonprincipal primitive theta with
1<r<T, all 1<=x<=2P and both endpoints of |tau|<=D,

    ||sum_n theta(n) Lambda(n) n^(i tau) g_B(x/n)||
      <= C P exp(-7U/6),
    C=4034437632 exp(1/4)+32 Cright+3689472>0.

Here g_B is the independently defined cumulative Gaussian weight and
Cright is the actual positive Mangoldt series at real part two. No new
analytic, zero-free, logarithmic-derivative, contour or convergence
hypothesis is added to the uniform theorem.

The actual right-line tail is at most 32 Cright P exp(-3U), and each
horizontal side is at most 1844736 P exp(-3U), uniformly for 1<=x<=2P.
The left-line budget extends over the entire same x range with twice its
previous constant. The exact arithmetic Mellin identity and the finite
rectangle equality then close the cumulative cancellation bound.

## Actual smoothing removal error

For every real width and positive argument, the actual weight satisfies
0<=g_B<=1, g_B(x)+g_B(1/x)=1 and g_B(1)=1/2. The scalar upper/lower step
errors equal actual Gaussian tail integrals. For B>0 and B epsilon>=1,
the proved distance bound away from the cut is

    |g_B(y)-1_{y>1}|
      <= (sqrt(pi))^(-1) y^2 exp(2/B^2-B^2 epsilon^2/2),
    epsilon>=0, |log y|>=epsilon.

The sharp Mangoldt sum is defined independently as the finite strict sum

    sum_{n<ceil(x)} theta(n) Lambda(n) n^(i tau),

which is exactly the sum over integer n<x, including the vanishing zero
term. At an integer cutoff the endpoint is excluded; the weight's half
value and the corresponding arithmetic error remain explicit.

For every complex character, including modulus-one principal, every real
tau, x>=1, B>0 and epsilon>=0 with B epsilon>=1, the actual two sums obey

    ||smoothed sum - sharp sum||
      <= (x(exp(epsilon)-exp(-epsilon))+2)(log x+epsilon)
         + Cright (sqrt(pi))^(-1) x^2
           exp(2/B^2-B^2 epsilon^2/2).

The actual difference is proved summable; near/far splitting is exact.
The far sum uses the proved identity sum Lambda(n)/n^2=Cright. The near
sum is a finite integer window, with cardinality at most its real length
plus two, and Lambda(n)<=log n supplies its bound. These error estimates
are unconditional arithmetic facts and do not claim cancellation for
the principal character.

Main sources: [PerronMangoldtWindow](../ZhangLS/Spec/Lemma56PerronMangoldtWindow.lean),
[PerronWeightBounds](../ZhangLS/Spec/Lemma56PerronWeightBounds.lean),
[PerronArithmeticError](../ZhangLS/Spec/Lemma56PerronArithmeticError.lean),
and [PerronNearError](../ZhangLS/Spec/Lemma56PerronNearError.lean).

## Verification

All fifteen module builds pass. The [regression](Step107Lemma56PerronWindowRegression.lean)
contains **14 expanded examples**: actual cumulative arithmetic series,
principal right-tail inclusion, both closed oscillatory endpoints,
super-Gaussian margin, global weight bounds/reflection, the scalar center,
strict integer endpoint, its actual half-weight error, closed distance
boundary, both independently defined actual smoothing sums, zero-index
near error, the expanded integer-cardinality bound, principal actual
error identity, and the empty epsilon-zero near set.
All [55 axiom reports](step107_regression_axioms.txt) use only `propext`,
`Classical.choice` and `Quot.sound`.

All **438 Lean sources** pass placeholder and structure checks. Coverage
is **301 trusted Spec modules and 379 project imports**, with **56 audit
regressions**. The strict static heuristic has the same **108 reviewed
candidates** as Step 106; no new candidate is introduced.
See [interface manifest](step107_interface_manifest.json),
[coverage](step107_coverage.json) and [static output](step107_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 301 trusted Spec
modules, the Spec aggregate, the full 379-import project and all 56
audit regressions passed. All 438 Lean fingerprints stayed unchanged.
Verification interval: 2026-10-01 16:33:40–16:58:53 Asia/Shanghai.
See [step107_kernel_verification.txt](step107_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt),
[source fingerprints](step107_source_fingerprints.json) and
[full gate log](step107_full_verification.log).

## Remaining original obligations

The promoted modules stop at the general smoothing-error formula.
The independently verified drafts below close the paper-scale smoothing
budget, sharp Mangoldt cancellation and prime-power removal outside this
project gate. The original prime-window result still requires conversion
to p^(1+i tau), actual prime-mass normalization and the faithful
modulus-one principal boundary. No completion of full Lemma 5.6 is claimed.
The complete 51-result goal remains active.

## Independently verified next-step draft

The independently verified [Step 108 draft](step108_lemma56_unsmoothing_draft.txt)
passes 11 standard-axiom interfaces and four expanded examples. It is
outside this frozen full-project gate. With B=exp(3U/2) and epsilon=exp(-7U/5),
the actual all-character smoothing error is at most C_err P exp(-7U/6),
where C_err=1728e+864+4Cright/sqrt(pi). Under original (A), the actual strict
sharp Mangoldt sum for distinct nonprincipal primitive characters is at most
C P exp(-7U/6), uniformly for all 1<=x<=2P and closed |tau|<=D.
The modulus-one principal error estimate and strict integer cuts are tested.
SHA256: `83c84e8662c8d41cf310ec857ef046b558a5101ddc129f064c63c8b28d75887f`. See [metadata](step108_lemma56_unsmoothing_draft_metadata.json)
and [kernel output](step108_lemma56_unsmoothing_draft.log).
The full original prime-window target is still unproved.

The independent [Step 109 combined draft](step109_lemma56_prime_power_draft.txt)
passes 17 interfaces (the preceding eleven plus six new interfaces) and
four expanded examples, again outside this project gate. The actual
all-character prime-power error is at most 2 sqrt(x) log(x), budgeted
into 1728 P exp(-7U/6). Actual strict-cut prime sums with log(p) weight
then satisfy C P exp(-7U/6), under original (A) for distinct nonprincipal
primitive characters, uniformly on all 1<=x<=2P and closed |tau|<=D.
SHA256: `9bbf7af00cc6d777fb7fdea95e7c1c4d41e0e458831209241f4d06c65965fb66`. See [metadata](step109_lemma56_prime_power_draft_metadata.json)
and [kernel output](step109_lemma56_prime_power_draft.log). The remaining
original obligations are the p^(1+i tau) weight, actual prime-mass
normalization and the faithful modulus-one principal boundary.
