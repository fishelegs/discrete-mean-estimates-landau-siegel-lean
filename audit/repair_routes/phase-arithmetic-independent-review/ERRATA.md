# Suggested additive clarifications to the frozen reports

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

Do not silently rewrite or replace the frozen derivation. Attach these clarifications and the independent review.

## 1. Label the existing Kl₂ expression as C₀

In PRIME_SIGN_AND_BILINEAR.md §2, after introducing the trilinear Kl₂ expression, add:

> This is the full-parity right-contour kernel for the original cross covariance C₀. More generally C_k contributes rψ^(k−1) after division by the two Z factors. For the proposed trial rψA+Zconj(B), k=1 and the root factors cancel: character orthogonality gives the congruence kernel ℓmn≡±1 modulo p, with the even principal-character subtraction. Consequently the Kl₂ theorem below does not evaluate C₁. The κβ coefficient, the gamma Mellin integral, the selected-family error, and the residue-conversion error remain in either calculation.

The target pairing T₁ is different again: after the residue factor it contains ε(χψ), hence a single-Gauss additive kernel. Use REVIEW.md §2 for its exact formula.

## 2. Strengthen, but do not overextend, the deletion scope

In DERIVATION.md §4, append:

> The d₈(D)/D bound is proved without squarefreeness. For every real primitive conductor D, its odd part is squarefree and v₂(D)∈{0,2,3}, so d₈(D)≪√D with an absolute constant. In fact if 4|D the removed terms already vanish: χ(2)=0 implies ρ(2^j)=0 for j≥2, and D|a implies 4|a. This concerns this deletion step only. The printed parity/conductor restrictions and the other errors in the BPZ argument still need separate treatment.

For other central-value parity kernels, the elementary bound |V(x)|≪(1+x)^(−2) is obtained by the same contour shift with the appropriate two gamma factors. Do not silently transfer the conclusion to derivative weights or high-height weights.

## 3. Preserve the limited meaning of the bare saving

Keep the exponent −3/200 and the arbitrary-coefficient interpretation. Add that extending the bound to shorter dyadic blocks is justified by orienting the smaller block as M and monotonicity of p^(−21/64)(MN)^(5/16), rather than asserting every block individually has the endpoint bracket p^(−.016). The bracket itself can worsen on shorter blocks, while the complete normalized estimate improves.

The final stopping paragraph should distinguish the missing C₁ congruence mean, its T₁ target mean, and the original C₀ Kloosterman mean. A calculation for one does not certify the others.
