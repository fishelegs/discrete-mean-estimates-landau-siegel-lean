# Admissible repairs and the full mixed-moment ratio

## Result and recommended next step

1. **Coefficient-only repair is blocked in all twelve previously audited finite models, even after correcting the optimization objective.** For every nonzero complex vector z=(z1,z2,z3,z4), the complete homogeneous ratio satisfies

   |ell(z)|^2 / (R Q(z)) < 1/2.

   This is a new standard-library rational-interval certificate, not a Lean theorem and not a theorem identifying the model with actual character means. It is stronger than the old constrained Q-minimum calculation because it lets the H11 coefficient vary and retains the actual mixed functional ell and the sharp tent norm R.
2. **3000 is only the paper's coarse J-norm budget.** The residue model dictated by the original tent and Lemmas10.1/10.2 gives exactly R=32/(pi h)+88 pi h/3 with h=.004, approximately2546.84770300835. The original coefficients give ell approximately5.15886588418+1.21048999487i.
3. **The existing normalization and interfaces do not supply independent pi, fixed-c-prime or core-beta tuning parameters.** Changing the core beta construction would require re-proving zero-spacing, positivity and residue-weight interfaces; other such constructions are not excluded. Free coefficients inside the twelve specified models have been tested with the full criterion. Correcting the actual B coefficient basis could change the true matrix M and is not excluded by this certificate.
4. **Do not start a numerical cutoff/frequency sweep yet.** The smallest constructive next obligation is a correct coefficient-basis reconstruction of the actual B in(12.2), followed by its true four basis-pair cross moments through Sections12–17. The Appendix B / Section15 basis discrepancy remains unresolved even at the original parameters. P7.1 and P14.1 are independent and should continue.
5. A conservative compact-width family is described below as a precisely constrained candidate for a later generalization, not as a family for which the current Q formula or analytic errors are already proved.

All files here are new. No live repository file, original certificate, GitHub state, definition, or completed theorem was edited. No Lean claim, new axiom, sorry, result-shaped assumption, or final not(A) argument is introduced.

## 1. Source identity and exact locators

Official source: arXiv:2211.02515v1, https://arxiv.org/abs/2211.02515v1 and https://arxiv.org/pdf/2211.02515v1 . PDF pages below are one-based printed/PDF pages.

- TeX `/tmp/zhang-2211.02515-source.tex`, SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- PDF `/tmp/zhang-2211.02515.pdf`, SHA256 `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`
- Positivity and mixed-moment reduction:(2.13)–(2.20), TeX469–556, PDF pp7–9
- Original H/J definitions:(2.21)–(2.30), TeX576–613, PDF p10
- P2.4/P2.5/P2.6 and(2.32)/(2.33):TeX630–661, PDF p11, visually verified
- P7.1 hypotheses(7.2) and conclusion:TeX1813–1850, PDF pp33–34
- L8.1 symmetrization:TeX2187–2189, PDF p42
- L8.2/L8.4 residue symbols:TeX2339–2415, PDF pp45–47
- Actual S_j-to-integral chain(8.10)–(8.12):TeX2436–2477, PDF pp47–48
- J/tent residue formulas L10.1/L10.2:TeX2719–2851, PDF pp53–57
- Four mixed moments and their combination:(10.12)–(10.17), TeX2953–3168, PDF pp58–62
- J duality L11.2:TeX3319–3352, PDF p65, visually verified
- H14/H15 and B:(12.1)/(12.2), TeX3360–3370, PDF p66
- Reflected tail and H16:(12.8)/(12.9), TeX3426–3455, PDF pp67–68
- Tail linearization/cancellation specializations:TeX3487–3508,3551–3590,3627–3649, PDF pp68–72
- P14.1:TeX3827–3843, PDF p76
- B support and coefficient-basis issue:(15.1)/(15.2), TeX3979–3984; convolution TeX4064–4070, PDF pp79–81
- Appendix B coefficient lemma15.1:TeX4273–4296, PDF p86; derivation TeX5281–5333, PDF pp107–108
- N/G support products:TeX1689–1703,4415,4812–4824, PDF pp30–31,89,98
- J norm arithmetic sums and coarse estimate:(18.3), TeX4917–4955, PDF p100, visually verified

The read-only live interfaces `Lemma111SmoothedTent.lean`, `Lemma112Approximation.lean`, and their completion reports retain the actual original tent, smoothing, conductor-Dp duality, D*t0 shift, and genuine error integral. They do not yet provide the aggregate J norm asymptotic below merely by being imported. The existing Section8 upstream audit fixes all original frequency limits, support shifts, conjugations, and pi factors.

## 2. The admissibility criterion is a ratio, not Q<.001

Let N=mathfrak(a)*mathcal(P)>0 and let dmu be the positive discrete measure C*(rho,psi)omega(rho). For any proposed H1,H2,J1,J2, define actual finite-D quantities

- Q_D = integral |H1+Z conjugate(H2)|^2 dmu / N
- R_D = integral |J1|^2 dmu / N
- S_D = integral |H2|^2 dmu / N
- E_D = integral |J1-Z conjugate(J2)|^2 dmu / N
- ell_D = integral [H1 conjugate(J1)+conjugate(H2)J2] dmu / N

The source identity(2.18) and Cauchy–Schwarz imply exactly

|ell_D| <= sqrt(Q_D R_D) + sqrt(S_D E_D).

A repaired contradiction requires genuine estimates with S_D bounded, E_D→0, and a strict limiting gap |ell|>sqrt(QR). For Q,R>0 this is |ell|^2/(QR)>1. If a model produces Q<0, that instead needs a separately valid positivity contradiction and all arithmetic bridges; it cannot be asserted from a floating model.

The paper's budgets |ell_D|>5, Q_D<.001, R_D<3000 force Xi2*/N<sqrt(3)<2. These are convenient budgets, not uniquely required constants. Retaining the lower bound5 and upper bound3000 would already permit any fixed limiting Q<25/3000=1/120 with a suitable error margin. The old Q-minimum>.024 result alone did not optimize this full criterion because ell changes with the coefficients.

Global scaling cannot help. To scale H1+Z conjugate(H2) by lambda, replace (H1,H2) by(lambda H1,conjugate(lambda)H2); Q and S scale by |lambda|^2 and ell by lambda. A compatible J scaling similarly changes R,E,ell and leaves the ratio unchanged. Scaling the positive measure also leaves it unchanged. Normalize ||z||=1 or ell=1 after proving ell nonzero; fixing z1=1 is only one projective chart.

Core beta1,beta2,beta3 and alpha=pi/logP are retained. The beta shifts arise from the zero-gap assertion and prove positivity of C*. Changing them changes the measure, positivity proof, residues, the P7.1 weights(1/2,2,3/2), and the Sections13–17 cancellations. The source's c-prime is an arbitrary sufficiently large fixed constant from the gap theorem; its perturbation tends to0 and is not a tunable leading-model parameter.

## 3. Reconstructing ell and R from the actual source sums

This section derives the **limiting residue model**, not a new character-sum asymptotic.

For a log-coordinate profile phi(t), write H_phi=sum chi(n)psi(n)n^(-s) phi(log n/logP). The original ramp profiles are

phi_(r,tau)(t)=(r-t)/r * exp(i*pi*tau*(r-t)) on0<=t<=r, and0 above r.

The original limiting triples are(r,tau)=(.504,1.5),(.5,2.5),(.498,1.5). At finite D the second r is .5-10 logT/logP; dropping this correction is a limit, not an exact identity. The original w is the real triangular height-one tent on[.5,.504], and the limiting reflected tent wR is on[.496,.5]. At finite D its support is shifted by alphaTilde=log(D*t0)/logP.

For j=1,2,3 put a+b=6-j, ab=(6,3,2)_j, and define

A_j phi(t) = -phi'(t)-i*pi*j*phi(t)
B_j psi(t) = -psi'(t)+i*pi*(6-j)*psi(t)-pi^2*ab*integral_[t,infinity] psi(u)du.

These formulas are forced by the actual source Dirichlet factors, not fitted:

- The first sum in S_j has local Mellin symbol L'(1,chi)(s-beta_j); after s rescales by logP this acts as A_j
- The second sum has local symbol L'(1,chi)(s+beta_(j+1))(s+beta_(j+2))/s, which acts as B_j
- Both factors carry1/logP; the arithmetic harmonic measure contributes logP; division by alpha contributes1/pi
- For a ramp, A_j phi=f_jtau(r-t)/r and B_j conjugate(phi)=g_jtau(r-t)/r, giving precisely the source f/g and every1/(r*r') denominator
- For the tent, A_j w is exactly the two branches of L10.1. B_j w is L10.2: below the support it is -pi^2 ab*h/2; on the rising and falling halves it gives respectively500(-1+y_1j) and500(1+y_2j), with the source y-functions. Thus the derivation includes the below-support contribution crucial for ell

Define the bilinear residue expression and its Hermitian symmetrization

K(phi,psi)=1/pi * sum_j q_j integral_0^infinity A_j phi(t) B_j psi(t)dt
T(phi,psi)=K(phi,conjugate(psi))+conjugate(K(psi,conjugate(phi))), q=(1/2,2,3/2).

L8.1 dictates this symmetrization. With
H1=z1 H11+z2 H12 and H2=conjugate(z3)H13+conjugate(z4)H12,

ell(z)=L1 z1+L2 z2+L3 z3+L4 z4,
L=(T(phi1,w),T(phi2,w),T(wR,phi3),T(wR,phi2)).

T is linear in its first variable and conjugate-linear in its second. Thus the first two components are H-to-J1 moments and the last two are J2-to-H moments, not the reverse. This matches the four source mixed moments(10.12)–(10.16) and(10.17). In particular L3 is around-5.1616, matching the source's dominant -8 iota3/(.498*pi), not an arbitrarily maintained lower bound5.

For any real compactly supported profile w with w(0)=0 and continuous zero endpoint values, integration by parts gives

Re integral A_j w B_j w = integral (w')^2 + 11*pi^2 integral w^2.

Indeed integral w'(t)integral_t^infinity w = integral w^2, and j(6-j)+ab=11. Therefore

T(w,w)=8/pi * integral (w')^2 + 88*pi * integral w^2.

For the height-one width-h tent, these integrals are4/h and h/3, so
R=T(w,w)=32/(pi*h)+88*pi*h/3.

This also explains why amplitude scaling or narrowing J without changing the rest of the construction is not a free improvement: R grows like1/h. A general real w need not be a tent, but changing it requires redoing the source L10.1/L10.2 and boundary estimates. The endpoint cancellation w(left)=w(right)=0 must be retained for the L-term in L11.2 to cancel.

Source-print caution: (18.3) omits C* on its left, although L8.1 and(2.33) require it, and its upper-half sum prints y_1j where L10.2 requires y_2j. The formula above is derived from the actual preceding S_j and L10.2, not from either inconsistent shorthand. PDF p100 visibly contains both inconsistencies. They do not justify changing any Section8 table.

## 4. New validated finite-model computation

`certify_ratio.py` uses only Python's standard library, exact rational fixed-point directed intervals at scale10^55, and degree80 Taylor enclosures for complex exponentials. Its arithmetic engine is copied, without execution of the original driver, from the already frozen Section18 certificate. `inputs/` contains byte-identical read-only copies of the original certified matrices and independent quadrature data. Their hashes are recorded.

`ratio_diagnostic.py` is a separate direct-integration implementation from the rational certificate. That one mpmath implementation was rerun at70 and100 digits; these are two precision runs, not two independent implementations. All ell coefficients, R, and all12 maxima from both runs are inside the rational intervals. The diagonal mean blocks reproduce the source c11,c22,c12,c33 and the structurally corrected c34 to the60-digit precision of the existing input. This is a cross-check, not an oracle used by the certificate.

Representative values:

L1=-.04751419447404+.03985419104558i
L2=.02152407921061-.01555824110745i
L3=-5.16159868017362+.00671124093284i
L4=.02147382054927-.01644102200906i
R=2546.8477030083465747...
ell(paper)=5.1588658841761975+1.2104899948749818i.

For any positive-definite model matrix M,

sup_(z != 0) |L^T z|^2/(R z*Mz) = L^T M^(-1) conjugate(L)/R.

Instead of trusting a numerical optimizer, the certificate proves positive definiteness by interval LDL of

A = [[M,conjugate(L)],[L^T,R/2]].

Its Schur complement is R/2-L^T M^(-1)conjugate(L)>0. Thus all four coefficients may vary, including z1=0, and the whole ratio is strictly below1/2. The minimal last-pivot lower bound exceeds217.

- All12 certified maxima lie between .32552033 and .41452914
- Representative `.5:exact:upstream` maximum lies in[.40716299028789405383,.40716299028789405384]
- Its paper-vector ratio is about .1992187720
- The largest branch maximum lies in[.41452913819742913056,.41452913819742913057]

Every original ambiguity is retained as the original audit's separate branch. The `.5:exact:upstream` branch is still an Appendix B terminal-expression model, not an established repaired actual L15.1. The new result does **not** certify the S_j asymptotics, Section12 low/high/transition passages, fixed-D errors, B coefficient reconstruction, or identification of M,ell,R with actual discrete means. It rules out coefficient-only repair inside these precisely specified models, not all mollifiers or all proofs.

Reproduction:

python3 -S audit/mollifier_ratio/certify_ratio.py

Optional independent checks (mpmath):
python3 audit/mollifier_ratio/ratio_diagnostic.py 70
python3 audit/mollifier_ratio/ratio_diagnostic.py 100

`ratio-certificate.json` contains all enclosures and five pivots for each branch. `ratio-certificate.log` is the successful replay output. Original frozen certificate checksums also passed in the live repository, read-only.

## 5. Which parameters may change, and what must follow them

### A. Fixed finite linear combinations: admissible algebra, exhausted model

Any fixed bounded z changes only finite linear combinations of the original three H kernels. All pointwise algebra, support bounds, and coefficient-size bounds survive. For true asymptotics one must prove the basis-pair identities once and propagate their errors with sum |z_i z_j|; one cannot reuse the numerical error evaluated at one vector. The mixed functional changes as above, and H2's moment must stay bounded. The new finite-model certificate makes more coefficient searching unproductive.

### B. Cutoffs and products: individual support is not enough

P7.1/L8.1 require bounded coefficients and each input supported below P T^-2. Every fixed cutoff exponent r<=1-eta satisfies this eventually, but this alone does not license the Sections12–17 cross moment.

Let c be the H14 cutoff exponent and let X2,X3 be the two H2 lengths. The true B length is at most

max(P^c,X2)*max(X3,X2).

At the source values c=.5, X2=P^.5 T^-10, X3=P^.498, this is P T^-10 for large D. N is supported below2T^2, and G below D^4; hence B*N is below2P T^-8 and B*G*N*N is below4P D^4 T^-6, which is below P T^-2 eventually. This supplies the source support savings used at TeX4044,4415,4812. Keep these product inequalities explicitly, including constant factors and D^4, rather than copying only the weaker displayed(15.2).

The full H11*H2 has length about P^1.004 T^-10, so it cannot replace B. Raising c above.5 by a fixed amount while leaving H2's P^.5 T^-10 term makes B too long. Lowering c could preserve lengths, but changes the dual tail upper endpoint to1-c and creates new overlap regimes. The conservative repair keeps c=.5.

For every changed H11 length P^r1, H15 is the exact original weight restricted to[P^.5,P^r1), not an independently selectable kernel. Its transformed tail is supported on[P^(1-r1)D*t0,P^.5 D*t0]. Both endpoints, the denominator r1, frequency phases, tail moments, and all low/high breakpoints must move together.

The T^-10 saving cannot simply be deleted, despite vanishing in the limiting numerical coordinates. Keeping it unchanged is the safest family. More generally a changed exponent K must still satisfy all displayed product inequalities; K>6 is a conservative sufficient leading saving for B*G*N*N when the other H2 term remains strictly shorter than sqrt(P), but this is not a proved generalization of every paper error bound.

### C. Frequencies: distinguish mollifier phases from the core beta shifts

For fixed real tau, the ramp coefficient has modulus<=1, so bounded real frequency perturbations preserve coefficient bounds. The source Mellin residue formulas extend algebraically by replacing beta_mu=i alpha tau everywhere. A sufficient safe exploratory compact set keeps tau away from0, the core limiting integers1,2,3, other chosen frequencies, and the contour radius5. For example compact neighborhoods strictly inside(1,2) and(2,3) avoid collisions. Separation from each other or j is a conservative condition for the existing residue proof route, not a claim that the exact kernel has a genuine singularity whenever two such values meet; some collisions are removable and require new treatment.

Changing tau alters every f/g coefficient, every E_j/E0 phase, the Appendix B functional, the Section12 exact residues, and ell. The source shortcut4 beta6-(beta1+beta2+beta3)=o(alpha) is special to tau6=3/2; likewise its other first-order phase identities depend on tau7=5/2. They cannot be retained after frequency changes. Fixed10^-5 linearization budgets are not uniform licenses. Use full exact residues and reprove the error estimate if frequencies are varied.

### D. J weights: retain conductor reflection and zero total derivative

For a real profile w supported on[a,b], require zero endpoint values and a bounded piecewise-smooth profile. The functional-equation dual is the reflected profile w(1-t+alphaTilde), supported on[1-b+alphaTilde,1-a+alphaTilde]. The equal adjacent intervals of the source tent are a simple way to make the L-term cancel exactly. J2 cannot be moved or scaled independently. For the symmetric tent on[.5,.5+h], reflection is exactly the source-style translated profile w(t+h-alphaTilde).

Existing L11.1/L11.2 prove the original profile. A generalized bounded family must supply uniform smoothing, boundary-mass, and discrete error estimates, not merely the exact formal duality. New polynomial weights change Mellin pole orders and all Section10/18 evaluations. A finite-dimensional bounded polynomial/spline span is a possible future target, but not an inherited theorem.

## 6. Smallest bounded nontrivial candidate family and its proof gate

A conservative **structurally admissible** one-parameter family, if a generalization is pursued, is

- fix0<h_min<=h<=.004 independently of D
- r1=.5+h, r3=.5-h/2, X2=P^.5 T^-10
- retain beta6=1.5 i alpha, beta7=2.5 i alpha and all core parameters
- retain H14 cutoff sqrt(P) and define H15 by the actual difference
- take the height-one tent on[.5,.5+h], midpoint.5+h/2, slope2/h
- reflect J2 using the exact D*t0 shift
- coefficients in a fixed bounded ball, with a proved nonzero ell normalization

This preserves the source ordering1-r1<r3<.5<r1, places r3 at the reflected midpoint, keeps the source B/N/G product savings, and stays inside the existing L11.2 z interval[.5,.504]. The restriction h>=h_min prevents the profile derivatives and J norm from blowing up while asserting uniformity. It is an economical family because it keeps the source's overlap topology and special frequency cancellations.

**It is not yet an analytically certified family, and no search of it was performed.** At minimum it needs:

1. Uniform ramp/tent coefficient and endpoint summation-to-integral identities for P7.1, supplying M's two diagonal blocks, ell(h), and R(h)
2. Parameterized L11.1/11.2 and the actual discrete E_D→0 estimate, using the reflected weight and original positive measure
3. A source-correct generalization of L15.1 for the actual coefficients of B, resolving the chi*psi versus psi basis at TeX3981/4070 before any reuse
4. Exact parameterized Section12 transformed-tail and Section15–17 basis-pair cross moments, including all normalization factors and errors; this supplies M's off-diagonal block
5. S_D=O(1), uniform error propagation on the chosen compact family, and a positive strict ratio margin certified after the formulas are justified

The present shortest repair research path is item3 at the original parameters, not a wider search. Even though P7.1 and P14.1 are general mean-value statements, neither substitutes for the specialized arithmetic reductions and error analysis of items1–4.

## 7. Remaining DAG and conservative feasibility

- P7.1 and P14.1: unchanged statements; both remain useful independent theorem targets
- L2.3 and core Sections3–6: untouched if only H/J profiles change within the stated support/phase bounds
- Fixed-profile sharp R and ell: need P7.1, accepted L8.1/L8.2/L10.1, the complete L8.4/L10.2 replacements and the actual arithmetic averaging/boundary residual; existing L11.1/L11.2 supply relevant genuine profile/duality infrastructure but not these means automatically
- P2.6: needs the discrete mass/error assembly as well as L11.1/L11.2 and a bounded actual H2 norm
- P2.5: still needs the true Section12 tail, L15.1 coefficient reconstruction, P14.1 and Sections13–17 assembly; the current numerical route is independently blocked
- A width/frequency/profile change adds parameterized analytic and numerical obligations; it must not overwrite original targets or certificates. A bounded family can keep previously proved generic lemmas, but fixed-parameter conclusions are not inherited merely by notation substitution

There is no demonstrated parameter repair. The complete fixed-basis ratio bound below1/2 leaves a substantial gap to the needed1, so rescaling, selecting different iotas, replacing3000 by the exact R, or optimizing the same four coefficients cannot rescue these models. Different profiles, different true cross terms established by a corrected analytic derivation, or a different construction remain open possibilities. Nothing here disproves the paper's main theorem or constructs a character satisfying(A). The51-node completion ledger is unchanged.

## Central publication review

The exact certificate was replayed in a separate central directory, reproducing ratio-certificate.json byte-for-byte. Independent source-formula transcription of(10.12)-(10.17) at85 digits is included as source_moment_check.py/json and falls within all four certified ell intervals. REVIEW.md gives the independent source, interval and Schur-complement review. The kernel is not involved in this numerical certificate.
