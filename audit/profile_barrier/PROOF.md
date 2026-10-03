# Supported profile functional: exact positivity and equality obstruction

Date: 2026-10-03. Independent read-only mathematical audit of the specified `.5:exact_model:upstream_tail` limiting model. This is an elementary functional identity/proof, accompanied by numerical diagnostics. It is **not** an actual-character mean theorem, a finite-D theorem, a Lean theorem, or an interval certificate. No shared proof file was changed.

## Verdict

The displayed Q and C are algebraically consistent with the selected source-residue model, with the stated orientation, integration tails, and endpoint conventions. More strongly, their joint form is positive semidefinite on the **entire stated supported profile class**. For the stated tent mixed functional,

    |L(phi,psi)|^2 <= R [Q(phi)+Q(psi)+2 Re C(phi,psi)].

Thus changing profiles while retaining this Q/C/R/L model cannot produce a strict leading ratio above 1 or a negative augmented Gram direction. This is a bounded obstruction to this limiting model, not to other arithmetic models, lower-order finite-D terms, or the intended main theorem.

The result is stronger than finite numerical probes and explains the observed approach to the reflected-tent equality direction. It supplies a stopping criterion: stop leading-profile numerical searches in this model. The genuine remaining repair work is actual mean identification and, if justified, a controlled finite-D expansion on the equality/null directions.

## 1. Scope and source audit

Use complex profiles phi, psi in H1 on the unit interval, supported in [0,.504] and [0,.5], respectively. Continuous piecewise C1 profiles with a finite partition and square-integrable derivative are an adequate subclass. In particular, they vanish continuously at their right endpoints. All formulas extend to these supported H1 profiles by continuity. Endpoint values at 0 need not vanish. Integrals below are Lebesgue integrals, and derivatives are weak derivatives where needed.

Source: `arXiv:2211.02515v1 TeX source`, SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.

- (2.21)-(2.27), lines 576-597: P1=P^.504, P2=P^.5 T^-10, P3=P^.498; beta6=3i alpha/2 and beta7=5i alpha/2; H2 uses conjugate iota coefficients. These frequencies have not been altered.
- (2.13), line 469: the actual beta1,beta2,beta3 contain distinct small perturbations. They are not identically i alpha j.
- (8.2)-(8.5), lines 2272-2282: the cross term is Z^-1 H1 H2. Thus C is complex bilinear in the actual profiles; its matrix location is M[H2,H1]=C after using the conjugate-coefficient convention for H2.
- Lemma 8.2, lines 2341-2345, and Lemma 8.4, lines 2392-2415: the residue multipliers give the F and G differential/Volterra factors used below. The weights q=(1/2,2,3/2) are the Proposition 7.1 weights, distinct from c=(3,3,1) in the cross base.
- (8.13)-(8.22), lines 2510-2545: substituting a source ramp reproduces the literal source f/g tables, including the displayed shifts. Section 9's selected `.5` denominator is the one obtained from its earlier product log(P2)log(P3).
- (12.9), line 3453, requires a term plus the conjugate of the reverse term. Lemmas 12.1-12.3 give the exact-model high integrals. The low-region term (12.12)/(12.15), lines 3610-3669, retains the integrated mass of the reflected H1 tail even where phi itself vanishes.
- Lemma 15.1, lines 4283-4296, and the terminal Appendix B calculation, lines 5323-5333: E_j(phi)=phi(0)-i pi j integral phi matches the source ramp residue. Truncating at .5 gives E_j^tr. This is specifically the upstream-tail branch selected in the assignment, not an assertion that all mutually inconsistent printed tail expressions are identical.
- (17.5), lines 4739-4745, yields the endpoint E0 product, with the coefficient interpretation already documented in the repository audit. Section 18 then produces -i times the c=(3,3,1) combination and the endpoint product.

The algebraic extension to general profiles means: define the residue operators F,G,E,A,B on those profiles and derive the identities below; their restriction to source ramps agrees with the specified finite model. It does **not** mean that checking four ramps proves a general arithmetic moment theorem. Even an extension by dense linear combinations needs uniform actual arithmetic errors before passing a limit.

## 2. Same-side form and its polarization

Put W_a(t)=integral_t^1 a(u)du, extending profiles by zero when appropriate. Let B be linear in its first argument and conjugate-linear in its second:

    B(a,b) = (8/pi) integral a' conjugate(b')
             +24i integral [a conjugate(b')-a' conjugate(b)]
             +88pi integral a conjugate(b)
             -12pi [a(0) conjugate(W_b(0))+W_a(0) conjugate(b(0))]
             +24i pi^2 integral [a conjugate(W_b)-W_a conjugate(b)].

Then B is Hermitian and B(a,a)=Q(a), with Q exactly as in the specified source model.

To verify directly from the source operators, define

    F_j(a)=-a'-i pi j a,
    conjugate(G_j(b))=-conjugate(b')+i pi(6-j)conjugate(b)
                      -pi^2 p_j conjugate(W_b),
    p=(6,3,2).

The source same-side expression is (1/pi) sum q_j integral F_j(a)conjugate(G_j(b)), plus the conjugate reverse term. The weighted sums are

    sum q=4, sum q*j=9, sum q*(6-j)=15,
    sum q*j*(6-j)=32, sum q*p=12, sum q*j*p=24.

In the diagonal, before the final integration by parts, this is

    (8/pi) integral |a'|^2 +48 integral Im(a' conjugate(a))
    +64pi integral |a|^2 +24pi Re integral a' conjugate(W_a)
    -48pi^2 integral Im(a conjugate(W_a)).

Since W_a'=-a and W_a(1)=0,

    Re integral a' conjugate(W_a)
       = -Re[a(0)conjugate(W_a(0))]+integral |a|^2.

This proves Q with its endpoint term; polarization proves B.

A useful single-interval transformation is f(t)=exp(3pi i t/2)W_a(t). Then

    Q(a)=(8/pi) integral [|f''|^2-(5pi^2/2)|f'|^2+(9pi^4/16)|f|^2]
         -12pi Re[f'(0)conjugate(f(0))].

For a supported in [0,r], f(r)=f'(r)=0. The natural left conditions are

    f''(0)+(3pi^2/4)f(0)=0,
    f'''(0)+(7pi^2/4)f'(0)=0.

The zero differential equation has natural-left solutions
4 cos^2(pi t/2)[C cos(pi t/2)+B sin(pi t/2)]. This correctly gives the clamped-right threshold r=1. It is **not** appropriate to substitute .504+.5=1.004 for the joined problem.

## 3. Exact cross gluing, including the tail

Write b=W_psi(0), a_low=integral_0^.5 phi, a_high=integral_.5^1 phi. In the cross integral put y(u)=psi(1-u), A(u)=integral_.5^u phi, and B0(u)=W_psi(1-u). Expanding the q sums gives

    C_base = -8i phi(0)psi(0)
             -12pi[phi(0)b+psi(0)a_low]+24i pi^2 a_low b,

and the integral integrand is

    (8/pi)phi' y' +24i(phi y'-phi' y)+64pi phi y
    -12pi[y'A+B0 phi']+24i pi^2[yA-B0 phi].

Integration by parts of the square-bracket term adds 24pi phi y to the integral and the endpoint contribution -12pi psi(0)a_high. At u=.5 its endpoint contribution vanishes because psi(.5)=W_psi(.5)=0. At u=1 it is generally nonzero.

Next A=a_high-W_phi. Its constant part adds 24i pi^2 a_high b. Both steps require keeping the region beyond supp(phi): A remains a_high there. Dropping that region invalidates this identity.

Now define

    q(t)=conjugate(psi(1-t)),   h(t)=phi(t)+q(t),  0<=t<=1.

W_q(t)=conjugate(b-W_psi(1-t)). Since q vanishes below .5, the resulting integral can be extended to all [0,1]. The exact cross identity is

    C(phi,psi)=B(phi,q)-8i phi(0)psi(0)-12pi psi(0)W_phi(0).

Also

    Q(q)=Q(psi)+24pi Re[psi(0)conjugate(b)].

Consequently the complete energy N is

    N(phi,psi)=Q(phi)+Q(psi)+2Re C(phi,psi)
             =Q(h)-24pi Re[h(1)conjugate(W_h(0))]
                   +16 Im[h(0)conjugate(h(1))].

This is a functional on the fixed unit interval. The overlap [.5,.504] changes how h is decomposed into phi and q, but contributes no missing length or extra overlap term.

## 4. Positivity, with a complete elementary proof

Set f=exp(3pi i t/2)W_h. Here f is H2 and f(1)=0; f'(1) need not vanish. The exact preceding identity becomes

    N = E(f)
      := (8/pi) integral_0^1 [|f''|^2-(5pi^2/2)|f'|^2+(9pi^4/16)|f|^2]
         -12pi Re[f'(0)conjugate(f(0))]
         -16 Re[f'(0)conjugate(f'(1))].

The Hermitian polarization of E has boundary terms with coefficients -6pi and -8, respectively. Integration by parts gives the interior operator

    (D^2+pi^2/4)(D^2+9pi^2/4)

and natural conditions

    f''(1)=pi f'(0),
    f''(0)+(3pi^2/4)f(0)+pi f'(1)=0,
    f'''(0)+(7pi^2/4)f'(0)=0,

along with the essential condition f(1)=0.

The three functions

    k1=cos(pi t/2),
    k2=cos(3pi t/2),
    k3=sin(pi t/2)+sin(3pi t/2)

satisfy the interior equation and all four conditions. Therefore their polarized pairing with **every** H2 test function v satisfying v(1)=0 is zero. This establishes nullity without presupposing positivity.

Subtract k=A k1+C k2+B k3, where

    A=3 f(0)/4-f'(1)/(2pi),
    C=f(0)/4+f'(1)/(2pi),
    B=f'(0)/(2pi).

Then g=f-k has g(0)=g'(0)=g(1)=g'(1)=0, and E(f)=E(g). Both explicit boundary terms vanish for g. Because g' has equal endpoint values and integral g'=0, the periodic mean-zero Wirtinger inequality gives

    integral |g''|^2 >= 4pi^2 integral |g'|^2.

It applies directly to the real and imaginary parts of the H1 function g'. Therefore

    E(f)=E(g)
      >= (3/pi) integral |g''|^2 +(9pi^3/2) integral |g|^2 >=0.

Equality holds precisely when g=0. Thus the kernel in f is exactly span{k1,k2,k3}. Equivalently the kernel in the glued h is

    span_C { exp(-i pi t), exp(-2i pi t), exp(-3i pi t) }.

The map between these spans is h=exp(-3pi i t/2)[(3pi i/2)f-f']. This also agrees structurally with the source's motivation using combinations of the three shifted L functions, but that observation is not used as a proof premise.

Important scope detail: the kernel of N as a form on **pairs** (phi,psi) is larger than three-dimensional. It also includes every supported overlap cancellation phi=-conjugate(psi(1-t)). The three-dimensional statement is for the quotient variable h. Error control for actual moments must not silently discard the overlap kernel.

An alternative positivity proof subtracts only [f'(0)/(2pi)]k3 and expands the result in the mixed Neumann-Dirichlet cosine basis cos((n+1/2)pi t). The first two weights vanish and all remaining weights are positive. The clamped/Wirtinger proof above avoids needing a spectral expansion at the proof stage.

## 5. The mixed functional and the full ratio

Let J be the real unit-height tent on [.5,.504], and J2(t)=J(1-t), the tent on [.496,.5]. Put M=integral J=.002 and

    L(phi,psi)=B(phi,J)+B(J2,psi),
    R=Q(J)=32/(pi*.004)+88pi*.004/3.

Let B_N denote the Hermitian polarization of the joined h energy. Because phi(1)=0 and J has both endpoint values zero,

    B_N(phi,J)=B(phi,J).

Reflection/conjugation gives

    B(q,J)=B(J2,psi)+12pi M conjugate(psi(0)).

The joined boundary correction in B_N(q,J) is exactly
-12pi M conjugate(psi(0)). Hence

    B_N(h,J)=L(phi,psi),     B_N(J,J)=R.

Positivity now implies the claimed full, scale-invariant inequality

    |L|^2 <= R N.

For N>0, equality holds exactly when

    h - (L/R)J is in span_C{exp(-i pi j t): j=1,2,3}.

All finite Gram matrices and their augmentation by J are consequently positive semidefinite when assembled from this functional. On a positive definite finite subspace the Schur residual can improve the ratio only toward 1. The exact reflected-tent linear combination is one equality realization. This is a proof for the prescribed limiting functional; no numerical or interval assumption is used in the inequality.

## 6. What is still needed for a repair

1. Finish the actual character-mean identification. Keep the original perturbed beta1,beta2,beta3, frequencies beta6,beta7, P2=P^.5 T^-10, the finite-D J2 displacement tilde-alpha, and all conductor/functional-equation phases. Restoring only one support displacement is insufficient for a next-order assertion.
2. Prove generalized residue/moment formulas with uniform errors controlled by explicit profile norms and coefficients. Source Proposition 7.1 assumes bounded coefficient sequences supported below PT^-2; the higher cross moment, tail, transition and Appendix B reductions impose additional obligations. The identities here do not discharge them.
3. If those actual means retain Q/C as their leading form, stop all attempts to find a strict **leading** margin inside this supported model: the theorem above excludes one. If an audited arithmetic correction changes a leading coefficient, rederive the joined identity for that genuinely changed model before another search.
4. A finite-D investigation should start from the exact equality/null structure, not generic near-collinear ramps. Choose a fixed, bounded decomposition of h into the two supports, for example a fixed smooth partition on [.5,.504]. Analyze a prescribed finite span of the three glued null modes, the target tent, and any specifically motivated overlap-cancellation direction. Include the original coefficients if needed for comparison. The error norm must control each side separately because gluing has its own overlap kernel.
5. For that bounded family, derive the first nonzero correction matrix, mixed vector and target norm together. Normalize the mixed functional and certify coefficient bounds. Use the positive complement/coercivity estimate above and an exact Schur complement to bound possible gains. A candidate is accepted only if a strict margin exceeds the fully propagated actual error, or a negative augmented Gram direction is certified with the same error control.
6. Stop that lower-order family when its corrected augmented Gram is certified positive semidefinite at the resolved order, or when the only apparent margin is below the proved error. This says nothing about unresolved higher orders or different analytic constructions. Equality of the leading form alone is not a finite-D impossibility theorem.

## 7. Reproducible checks

The initial high-precision transcription diagnostics were followed by a separate, self-contained exact implementation. Run `python audit/profile_barrier/check_independent.py`; its26 checks and scope are recorded in `exact-checks.json` and the independent review. These finite symbolic checks support the displayed identities; the functional argument above establishes positivity for the entire stated class. Neither proves an actual arithmetic mean identity or a Lean theorem.

## 8. A specifically bounded finite-D route, still unproved

The finite-D analysis must retain the actual relative beta offsets and the Dp-versus-p conductor change at the same scale. The source has L=log D, log P=L^9, alpha=pi/log P, and beta_j in (2.13). Thus alpha L is of order L^-8 and log D/log P=L^-8. These terms must be analyzed together. The displacement 10log T/log P=10L^-7.9 from T=exp(L^1.1) is slightly larger and cannot simply be forgotten for endpoint profiles; log t0/log P=519log L/L^9 is smaller but remains relevant if earlier orders cancel.

A bounded candidate avoids a moving endpoint by taking a fixed smooth partition chi with chi=1 on [0,.501] and chi=0 on [.503,1]. For each of the three null modes h_j(t)=exp(-i pi j t), define phi_j=chi h_j and q_j=(1-chi)h_j, then psi_j(t)=conjugate(q_j(1-t)). This gives phi_j supported below .503 and psi_j below .499, hence a strict fixed gap from .504 and, eventually, .5-10log T/log P. This is a specified three-dimensional leading null family. Its generalized actual arithmetic interface is unproved; writing down these profiles does not import an existing beta6/beta7 ramp theorem. If maintaining a fixed modulation convention, record these complex envelopes explicitly and prove their corresponding interface.

The next question is whether the actual finite-D form restricted to this family has a negative first nonzero eigenvalue with normalized remainder o(L^-8), or at whatever earlier/later order actually survives. No perturbation matrix is guessed here. The needed matrix must include arithmetic corrections, actual phases, conductor changes, and all mean-identification terms at the chosen order. The current o(1) and coarse relative budgets cannot decide it. A failure to prove the requisite remainder bounds is a blocked research route, not evidence of a favorable sign.
