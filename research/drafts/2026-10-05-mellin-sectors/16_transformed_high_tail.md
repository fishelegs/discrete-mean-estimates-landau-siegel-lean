# Paying the actual transformed high covariance tail

Draft research note dated 2026-10-05. Independently source-reviewed for the entire actual transformed high covariance tail; not Lean-certified. This note concerns the post-AFE transformed integer arguments of the actual Gaussian-log target. It is distinct from the already accepted tail in the ORIGINAL polynomial output, even though the final numerical bound has the same exponents. No original-output theorem is transferred to a dual variable.

## 1. Exact object and result

Keep the original finite inverse X=D^4, L=log D, B=log P=L^9, alpha=1/B, all actual imaginary beta shifts, the real primitive chi, both parities, the original prime window P<p<P(1+L^-68), original V4 and all exact Gaussian-target branch weights. The original time measure is

    dmu(t)=1_(|t-t_c|<=H) exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    t_c=2pi L^519, W=L^400, H=L^405.

For each branch ij define, on its two original post-AFE tuples,

    X_ij=d m^(1-i)n^(1-j)(m')^i(n')^j,
    Y_ij=e m^i n^j(m')^(1-i)(n')^(1-j).

Let T_ij,high(Y0) be the exact same-branch covariance contribution with

    max(X_ij,Y_ij)>Y0,  Y0=P^2 D^5.              (1.1)

It uses the FULL nonprincipal parity kernel, with its p-unit mask:

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0)

on p-units and zero otherwise. We prove for every ij

    |T_ij,high(Y0)|
       <<P^2 D^-7 L^24836 (log L)^6+P^-18
       =o(P^2).                                (1.2)

The proof pays the entire quadratic tail, including its high/low crosses, by exact full-K rectangles and the accepted absolute far-ratio estimate. It neither bounds only a pointwise W weight nor discards an arbitrary restriction of an already bounded signed covariance. Every infinite dyadic shell is included.

## 2. Comparable full rectangles and the paid far remainder

Put delta=L^-395, I_-1=(Y0/2,Y0], and

    I_j=(2^j Y0,2^(j+1)Y0], j>=0.

Let E be the disjoint union of the ordered Cartesian rectangles

    I_j x I_j, I_j x I_(j-1), I_(j-1) x I_j, j>=0. (2.1)

Each rectangle is contained in the high sector (1.1). Conversely any pair in the high sector but outside E has ratio of the larger to the smaller at least 2, with the strict endpoint conventions giving no relevant ambiguity. Indeed if the smaller is <=Y0/2 and the larger >Y0, this is immediate; otherwise their dyadic labels differ by at least two. Hence

    |log(Y_ij/X_ij)|>=log 2>delta                (2.2)

for every omitted tuple eventually.

The accepted same-branch localization proof bounds the contribution of ANY bounded tuple restriction of its far region by O(P^-18). Its infinite-index and outer-height tails are paid absolutely; on the retained finite indices/heights its time contour estimate is taken in absolute value for each tuple before summation. Thus it applies to the high sector minus E with the complete original kernel and both parities. It follows that

    T_ij,high(Y0)=sum_(rectangles in (2.1)) T_ij(rectangle)+O(P^-18). (2.3)

The complete rectangles may themselves contain far pairs. They retain those pairs; no near-ratio indicator is inserted into the bilinear sieve estimate. The ratio geometry alone is used to pay what is outside the union. This argument works at all transformed output sizes without identifying them with original input or output variables.

## 3. Open the actual AFE weights on a fixed positive line

For each copy c=1,2 keep the original outer lines

    z_c=alpha+i v_c, w_nu,c=-alpha+i y_nu,c,
    w_23,c=-alpha+i y_23,c, kappa_F,c=z_c+w_F,c.

All pair arguments s+kappa_F,c are exactly critical for real original t, at every outer height. Fix an integer J>=2. Move each of the four degree-two AFE inner contours from real part 2 to real part J; for J=2 no move is needed. This rightward move crosses neither the kernel pole at zero nor a gamma pole. For fixed outer labels, the inner Gaussian pays the horizontal sides. The global integrable envelope proved in Section 4 then justifies all subsequent interchanges.

Write omega_F,c=J+i x_F,c. Relabel m,m' if i=1 and n,n' if j=1. Exactly as in the accepted finite-rectangle identity, X_ij=k=dmn and Y_ij=ell=em'n'. For a pair with bit epsilon,

    epsilon=0: eta_F,A=kappa_F,1+omega_F,1,
               eta_F,B=kappa_F,2+omega_F,2;
    epsilon=1: eta_F,A=kappa_F,2+conjugate(omega_F,2),
               eta_F,B=kappa_F,1+conjugate(omega_F,1).

Now all four eta parameters have REAL PART J. The exact grouped coefficients are

    A_J(k)=sum_(dmn=k,d<=X) upsilon(d)d^(-w_nu,1)
              nu_beta(m)m^(-eta_nu,A)d23(n)n^(-eta_23,A),
    B_J(ell)=sum_(em'n'=ell,e<=X) upsilon(e)e^(-w_nu,2)
              nu_beta(m')(m')^(-eta_nu,B)d23(n')(n')^(-eta_23,B). (3.1)

They are common across p, psi and t at fixed Mellin labels. No inner-divisor input mask occurs: these are the actual infinite-index Gaussian-target branch expansions, whose original input/output extensions were already justified by the accepted norm reduction. We have NOT imposed the convenient artificial post-AFE cutoff P^3 in this proof.

The literal finite inverse gives, for every k>=1 and every height,

    |A_J(k)|,|B_J(k)|
       <=X^(J+alpha) k^-J tau_6(k)
       <=2(X/k)^J tau_6(k),                     (3.2)

eventually. To see this, d^alpha m^-J n^-J=d^(J+alpha) k^-J, d<=X, and |upsilon|,|nu_beta|,|d23|<=tau_2. There is no infinite-inverse substitution or reciprocal input in (3.2).

On a finite rectangle the exact covariance is the ten-height integral of

    sum_(p,a,psi nonprincipal parity a) integral
       S_ij,J(p,a,t;lambda) A_I(psi,t)
                                    conjugate(B_I'(psi,t))dmu(t), (3.3)

where the polynomials have coefficients A_J(k)/sqrt(k), B_J(ell)/sqrt(ell) and factors psi(k)k^-it. Reverse parity covariance before applying estimates: (3.3) retains exactly the full K and all p-unit zeros. The scalar is independent of the particular psi in a fixed parity. Actual gamma phases remain in this identity.

## 4. Global fixed-line gamma bound, including all Mellin heights

Set T_* = 1+t_c+H, Q_* = 2P T_*, Q_nu,* = sqrt(D)Q_*. These dominate the actual conductors p/pi and p sqrt(D)/pi times the time scale by absolute constants. Define

    T0=X Q_nu,* Q_* <<P^2 D^(9/2)L^1038.        (4.1)

Here T0 is a positive scale, not the original time variable or output cutoff.

For sigma in {1/4,3/4}, every real T,x and the fixed imaginary shift represented by real b=O(1/B), two-sided fixed-strip gamma estimates give

    |Gamma(sigma+J/2+i(T+b+x)/2)
                   /Gamma(sigma+i(T+b)/2)|
       <<_J (1+|T+b|)^(J/2)
               (1+|x|)^(J/2+1/4) exp(pi|x|/4). (4.2)

For clarity, use the global fixed-real-part bound

    |Gamma(u+iy)| comparable_u (1+|y|)^(u-1/2)exp(-pi|y|/2), u>0.

In the numerator u=sigma+J/2, so u-1/2>=0. The inequality

    1+|T+b+x| <=(1+|T+b|)(1+|x|)

then combines the numerator polynomial power with the reciprocal denominator power to give exactly J/2 in (1+|T+b|), even when the latter reciprocal power is negative. The exponential quotient is at most exp(pi|x|/4). Thus (4.2) is uniform even when an outer height cancels t or when x cancels the pair height. This is not a central-height-only estimate.

For a two-gamma AFE pair the product of (4.2), its conductor C^omega and its Gaussian kernel e^(omega^2)/omega is bounded by

    C_J C^J (1+|T|)^J
       (1+|x|)^(J+1/2) exp(-x^2+pi|x|/2)/sqrt(J^2+x^2). (4.3)

Since T is either sign of t+v_c+y_F,c plus a fixed O(1/B) shift,

    1+|T| <<T_* (1+|v_c|+|y_F,c|).

Every root-free FE scalar has modulus exactly one at the critical pair argument for real t, for all outer heights and either parity; this also covers B11. The original H4 and both Gaussian lower-mask kernels have every fixed polynomial height moment O(log(2B)). Thus after the four pair estimates (4.3), the entire exact scalar has an envelope

    |S_ij,J(p,a,t;lambda)|
       <<_J (Q_nu,* Q_*)^(2J) H_J(lambda),
    integral_(R^10) H_J(lambda)d lambda/(2pi)^10
       <<_J (log(2B))^6.                        (4.4)

There are six outer contours with small denominators; the four inner contours now have real part J, so their Gaussian moments are constants depending only on J. Fixed polynomial factors in all outer heights are allowed by the accepted H4/profile moment bounds. No height truncation, additional t_c power, forbidden reciprocal range or silently discarded canceled-height region is used.

The underlying gamma estimate is the ordinary fixed-strip Stirling interface already used in the accepted AFE proofs. The displayed derivation makes its full-height uniformity explicit. All relevant gamma arguments have positive real parts on the real original t and these contours. We make no complex-time deformation on the J line; the separately accepted far estimate is applied to the exact W object before this change of representation.

For fixed J>=2, (3.2) gives absolute summability of the infinite coefficient polynomials against k^-1/2. Together with (4.4), this also justifies opening, relabeling, and interchanging the infinite tuple sums and contour integrals. There is no reliance on conditional rearrangement of an infinite covariance.

## 5. Full-K hybrid bound on one comparable rectangle

Write Y_j=2^jY0. In each of the three rectangles indexed by j in (2.1), both variables lie between Y_j/2 and 2Y_j. The elementary global harmonic divisor bound and tau_6^2<=tau_36 give, from (3.2),

    sum_(k in either interval) |A_J(k)|^2/k
       <<_J (X/Y_j)^(2J)(log(2Y_j))^36,         (5.1)

and likewise for B_J. In (5.1) the possible factor 2^(2J) from the lower endpoint is part of the constant depending on fixed J.

For each fixed height vector, apply pointwise scalar domination (4.4), Cauchy on the actual family/time measure, and the accepted normalized Gaussian hybrid large sieve with maximum polynomial length 2Y_j. This gives, after integrating all heights,

    |T_ij(rectangle)|
       <<_J (P^2+Y_j/W)(T0/Y_j)^(2J)
                    (log(2Y_j))^36(log(2B))^6. (5.2)

The two coefficient energies enter as their geometric mean, not as their product. The conductor factor in (4.4) combines with the finite inverse X from (5.1) to produce exactly T0^(2J). Pure p phases are harmless under pointwise scalar Cauchy, and no p derivatives or sparse-prime norm replacement are used. The full principal subtraction is still inside the covariance represented by (3.3).

This is an attached bilinear polynomial estimate. The proof does not replace the W weights by positive pointwise bounds inside a signed norm and then assume a large-sieve inequality for an unproved common coefficient sequence.

## 6. Sum every infinite shell

Since log Y0=2B+5L, for all j>=0

    log(2Y_j) <<B+j+1,
    T0/Y_j <<2^-j D^-1/2 L^1038.

The complete sum of (5.2), including all three ordered rectangles at each j, is at most a constant depending on J times

    P^2 D^-J L^(2076J)(log(2B))^6
      sum_(j>=0) [1+2^j D^5/W] 2^(-2Jj)(B+j+1)^36. (6.1)

The polynomial shell factor is retained explicitly. For fixed J>=2,

    sum_(j>=0) 2^(-(2J-1)j)(B+j+1)^36 <<_J B^36.

Eventually D^5/W>=1, so (6.1) is

    <<_J P^2 D^(5-J) L^(2076J-400) B^36(log(2B))^6
     <<_J P^2 D^(5-J) L^(2076J-76)(log L)^6.    (6.2)

At J=12 the exponent 2076*12-76 equals 24836 and 5-12=-7. This proves (1.2), after the far remainder in (2.3). Because D=exp(L), D^-7 dominates every fixed power of L, so the entire right side is o(P^2). The argument includes outputs beyond every fixed P power; no endpoint bound replaces the infinite sum.

## 7. Scope and bounded transformed middle

The new payment is for max(X_ij,Y_ij)>P^2D^5 in the actual transformed covariance. It is NOT the already accepted original-output tail and is not obtained by identifying a dual index with an original one. Both high/low orientations and all three full rectangles at every shell are included. Its restricted principal means have not been separately bounded or deleted.

Combined with the accepted small-rectangle payment and the independently accepted [mixed-boundary proof](15_mixed_transformed_boundary.md), the sufficient remaining full-K target can be restricted to

    M<X_ij,Y_ij<=Y0, X_ij!=Y_ij,
    |log(Y_ij/X_ij)|<=delta,
    M=P^2 L^402, Y0=P^2 D^5.                    (7.1)

Here is exact bookkeeping. The LL sector relative to M decomposes into the bounded square (M,Y0]^2 and its high part. Its high part differs from (1.1) only by high mixed tuples with min(X_ij,Y_ij)<=M; these have ratio at least Y0/M, which exceeds exp(delta) eventually, and hence are absolutely paid far tuples. Within the bounded square the far contribution is paid and the equality part is bounded by the explicit positive arithmetic majorant of the accepted diagonal proof. No arbitrary signed-subset monotonicity is used.

Thus, using that accepted mixed-boundary result, if Z_ij denotes the exact full-K contribution in (7.1),

    sum_(i,j)||B_ij||_H^2
       =Re sum_(i,j)Z_ij
          +O(P^2 L^(958/15)(log L)^(82/5)).      (7.2)

The restricted principal subtraction stays inside Z_ij, along with both positive and reflected congruences and every original prime/parity/p-unit mask. A one-sided aggregate sub64 upper bound for Re sum Z_ij remains sufficient by the pointwise unit-root inequality and accepted norm transfers. No bound for this middle correlation, no full balanced estimate and no signed half-threshold conclusion are proved here.

## 8. Verification

SOURCE_PINS.json identifies exact accepted interfaces. The main high-tail theorem in Sections 1-6 does not depend on the mixed-boundary theorem; the combined consequence (7.2) uses its separate, now-completed source acceptance. The exact source and acceptance identities are recorded in [SOURCE_PINS.json](SOURCE_PINS.json). Diagnostics check the disjoint dyadic geometry, literal coefficients on Re omega=J for all four branches, full-K finite-rectangle identities, global gamma comparisons including height cancellation, shell summability and the exact exponent ledger. They are consistency checks, not mathematical certification or an A2022 numerical example.
