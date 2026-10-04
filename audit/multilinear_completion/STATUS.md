# Source status: accepted selected HB j=2 component

The finite J=4 Möbius decomposition is exact for the actual shifted coefficient. For the selected j=2 component, two smooth completions give C′,Y′≤P^3.003/(BR), E(C′)≪L^324, E(D′)≪L^(−1551/2), and

    |Δ_selected| ≪ a_norm^−1 L^(−127/4) max(1,P^1.003/(BR))
                   + O(a_norm^−1 P^−10).

For a collection of blocks use the supremum of the maximum factor. BR≥P^(5/6) improves the component power loss from .501 to .17; BR≥P^1.01 makes the entire selected component o(1). The j=1,3,4 components, j=2 complement, global signed half threshold, and exponent-2024 theorem remain open.

Read [PROOF.md](PROOF.md) for the full source proof and [REVIEW.md](REVIEW.md) for independent acceptance and detailed hypotheses. This is not Lean certification. The independent checker freshly passes 53,354 assertions, with 22 public input pins and two historical-to-public mappings verified. The author REPORT was recovered byte-exact. Eight original archival artifacts remain unavailable, and the author checker was not rerun. The derived editions have new hashes, with original-source mappings in [PROVENANCE.json](PROVENANCE.json).

## Reproduce

Python 3 and the pinned repository inputs are sufficient; no compiler, third-party Python package, network request, or missing archive is required.

    python3 verify_bundle.py --repo-root /path/to/repository --rerun

The verifier checks the package manifest, repository bytes, public ancestry mappings, machine-readable scope, and fresh independent checks. The source commit is recorded in INPUTS.json; a later repository HEAD is allowed only when all pinned input bytes still match. Its report distinguishes finite checks, source acceptance, historical availability, and the open global theorem.
