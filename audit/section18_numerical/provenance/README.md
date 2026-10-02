# Original audit provenance

The `original/` directory preserves all thirteen files from the original frozen
audit byte-for-byte, including its original manifest and SHA256SUMS. Those files
are historical evidence, not the current publication instructions. Use the active
README, DERIVATION, and integration_manifest one level above for the portable
commands and current scope. In particular, current documentation supersedes the
original wording about repaired arithmetic formulas and formal verification.

Original integrity can be checked independently:

    cd audit/section18_numerical/provenance/original
    sha256sum -c SHA256SUMS

The original absolute temporary paths are preserved here intentionally as
provenance. Do not execute the archived Python copies; use the active copies.
