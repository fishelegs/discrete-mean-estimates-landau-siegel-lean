# Explicit Lemma5.6 source-use scope

Source: official arXiv2211.02515v1 TeX, SHA2565dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b; original statement is PDF page29, TeX1579–1583.

The printed statement says primitive theta modulo r, r<T and theta different from chi. It does not explicitly exclude the primitive modulus-one character. The repository preserves that literal range in Lemma56Target. At r=1,t=0 the actual sum norm is exactly the positive prime mass; `lemma56_principal_paper_sum_zero_height` and `lemma56_principal_paper_decay_requires_absorption` expose the resulting required inequality1<=C*decay. This is a boundary/scope issue, not a constructed counterexample satisfying(A), and the full literal target has not been analytically proved.

The already proved source-faithful restricted port is `lemma56_uniform_primitive_prime_window_normalized_bound` in Lemma56ActualPrimeMassNormalization.lean. It explicitly requires1<q, primitivity, the true difference from chi, q<T and the original closed height bound. No final not-(A) result is used to obtain it.

All explicit later citations found in the original TeX were checked:

- Section7, line2014: explicitly1<r<D. The actual small-conductor route uses the nonprincipal port
- Section8, line2362: the integrand is L(1-beta_j+s,chi), whereas printed5.6 excludes theta=chi. This citation cannot justify that step. The published complete Lemma8.2 uses an independent actual Abel/Taylor proof, whose header records the misreference and actual5.8 input
- Section14, line3963: explicitly1<r<D^3, after principal and chi-induced level-character branches are separated. The actual implementation proves conductor/inducer distinctions and applies the nonprincipal port; its principal contribution is a separate estimate

This audit covers explicit source citations and the named currently verified interfaces. It does not declare all unfinished downstream assemblies proved. Merely deriving the literal all-primitive statement ex falso from a future final contradiction would not verify its claimed analytic estimate and will not be counted as source-level validation. The main chain must continue through the independently proved restricted port and actual principal/main-term branches.
