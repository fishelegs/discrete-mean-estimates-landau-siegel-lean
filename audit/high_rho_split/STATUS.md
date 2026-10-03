# High-rho small-rare-part split

**Accepted at source level on 2026-10-03.** The complete [proof](PROOF.md) and final [independent review](INDEPENDENT_REVIEW.md) establish an additional absolute-error reduction under the unchanged original assumption `(A): L(1,chi)<(log D)^-2022`.

Define `b_chi(v)` as the product of the full prime powers in v whose primes satisfy `chi(ell) in {0,1}`. In the existing high-rho sum, retain the original Long labels, the original whole-label condition `2K>P^(99/100)`, every original mask and cutoff, both profiles, and the mollifier's literal `D does not divide d` deletion. The exact coefficient partition at `b_chi(v)<=P^(1/100)` gives

    |Delta_small-rare| << a^-1 P^-1/200,
    Delta_rho,high = Delta_large-rare + O(a^-1 P^-1/200).

All quadratic characters in the actual family are included. Their principal images under character squaring contribute the explicitly paid `+P` in the fourth moment. Every family mean retains its full natural-length cost `(P^2+Y)`. No signed extension from Psi1 to the full family is made.

On the nonzero rho support, the ramified part is at most `D^21`. Thus the remaining `chi(ell)=1` prime part is strictly greater than `P^.01/D^21>P^.009` eventually. This does not assert that one prime factor exceeds that threshold.

The accepted sparse reduction therefore becomes

    I_left^X = J_right^infinity + Delta_large-rare
      + O(a^-1 L^-187/4) + O(a^-1 P^-1/200) + O(exp(-c L^10)).

The separately [accepted half-norm comparison](../half_norm_constant/STATUS.md) gives `Re J_right^infinity=Im R_D=(1/2)m_H+o(1)`. The remaining sufficient signed estimate is

    Re Delta_large-rare <= (1/2-epsilon)m_H + o(1),

for fixed epsilon>0. That bound is not proved. Neither a full rare-part signed bound nor a strict gain is claimed. The source exponent 2022 and distinct final target exponent 2024 are unchanged. This package is source-only; it is not a Lean certificate or a transitive axiom-closure certificate.

The external prime-distribution papers are discussed only to delimit applicability. They do not supply the required shared-coefficient rho mixed mean. In particular, the older Wright progression range keeps both `sqrt(x)<q` and the `D^-1` factor in the upper bound.

Run `python3 verify_bundle.py --require-accepted`. Add `--repo PATH` to check exact repository and accepted dependency source pins. See [REPRODUCE.md](REPRODUCE.md).
