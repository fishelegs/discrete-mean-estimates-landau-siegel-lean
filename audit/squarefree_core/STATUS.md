# High-rho squarefree-kernel reduction

**Independently accepted at source level on 2026-10-03.** The [proof](PROOF.md) and [independent review](INDEPENDENT_REVIEW.md) establish

    Delta_rho,high = Delta_squarefree-large + O(a^-1 P^-1/100).

The paid selector is the unique squarefree kernel s(v)<=P^(3/20), where v=t²s(v). Common factors of t and s(v), repeated split primes, ramification, the strict internal e>D^20 cutoff, all original Long/high labels, both profile masks, the actual Psi1 family and literal mollifier deletion are retained. The complementary odd-valuation split-prime product exceeds P^.149 eventually; this is a product condition and does not assert one large prime factor.

The two completion regimes use the fixed transition K=P^(7/5). Their worst powers are -21/1000 and -253/6000, with logarithmic costs 2215/2<1200 and 2741<3000. Every natural-length P²+Y loss and the quadratic-character principal-image +P term is paid. The finite independent checker covers 81,920 actual coefficient cases; the written analytic proof, not those finite checks alone, justifies the uniform result.

With the [accepted half-norm constant](../half_norm_constant/STATUS.md), the outstanding signed condition remains

    Re Delta_squarefree-large <= (1/2-epsilon)m_H + o(1)

for fixed epsilon>0. It is not proved. The new absolute error is smaller than the existing O(a^-1 L^-11/2) combined error and does not itself provide strict gain. The original hypothesis exponent 2022 and final target exponent 2024 are unchanged. This source-only package adds no completed numbered theorem; the ledger remains 40/51.

Run `python3 verify_bundle.py --repo ../..` from this directory. [Reproduction instructions](REPRODUCE.md) distinguish exact finite checks, source pins and the unformalized analytic proof.
