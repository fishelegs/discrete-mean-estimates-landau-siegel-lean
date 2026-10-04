# Actual lambda replacement and weighted outer propagation

Three modules prove replacement of the original complex Lambda factors by the exact totient baseline and propagate the error through the actual character-weighted outer sum. Every original shift and prime factor is retained, including p=2 and n=1.

For each fixed c>0, one constant and modulus threshold precede D,j,n. For B=log P and log n<=201B/400, the actual relative product error is bounded by C(1+log B)^2/B, with explicit witness C=384*pi*exp(1). The proof derives every denominator lower bound and uses the elementary prime-log split and finite-product exponential inequality. It assumes no target approximation.

For each fixed bound M>=0, the outer theorem uniformly covers every actual real primitive character, all three j, and every bounded complex K with the stated support. It retains the literal L'(1,chi)^2/B^2 scalar and replaces norm(chi(n))*Lambda_j(n)/phi(n) by norm(chi(n))*phi(n)/n^2. Its error is C*L^4*(1+log B)^2/B^2. This result does not need hypothesis (A). It does not evaluate the resulting coprime sum or prove the actual m_H limit.

## Verification

All five branch files are byte-identical to the independently verified branch. Three proof modules, two required dependencies, and all12 named regressions compiled centrally. Complete provenance covers68 declarations:53 proof-owned and15 regression-owned, including all generated declarations. The often quoted60 was the four-module outer audit subset and excluded eight declarations owned by the earlier regression module.

Every complete type, owner, universe list, reference hash and transitive axiom set is checked. Only propext, Classical.choice and Quot.sound occur. The independent semantic review confirms the actual local factors, totients, character/scalar weighting, endpoints and quantifier order. The installed portable reproducer subsequently passed all8 compiler invocations and the full evidence verifier.

[Detailed evidence and review](lambda_replacement/README.md) · [Portable reproduction receipt](CLOUD_LAMBDA_PORTABLE_REPRODUCTION.json)

Remaining fixed-H obligations include the actual complex Abel evaluation, profile-kernel uniform derivative bounds, exact arithmetic normalization and same-c zero-mean assembly. This milestone establishes neither the actual m_H positive asymptotic nor the remaining strict signed upper bound. The original numbered ledger stays37 original plus3 repaired statements,40/51. Fresh whole-repository verification is separate.
