# Actual Λ replacement: independent central evidence

**PASS.** The five exact exported files were checked against the applied checkout,
and three proof modules plus two regression modules were compiled independently
with Lean 4.30.0, one thread, and `-M4096`. Two missing cached prerequisites were
also rebuilt privately. All compiler outputs went into a private overlay; cached
dependencies were linked read-only. No Lake, shared-cache writes, aggregate
builds, repository edits, or publication were performed by this reviewer.

The complete package owns **68 declarations: 34 explicit and 34 generated**.
The proof files own 53 (22 explicit + 31 generated); the two regression files own
15 (12 named tests + 3 generated declarations). The author's reported 60 was the
outer audit's four-module subset, which excludes the earlier regression's eight.

| Defining module | Owned | Explicit | Generated |
|---|---:|---:|---:|
| FixedHLambdaReplacementLocal | 15 | 8 | 7 |
| FixedHLambdaReplacement | 12 | 5 | 7 |
| FixedHLambdaReplacementOuter | 26 | 9 | 17 |
| audit.FixedHLambdaReplacementRegression | 8 | 7 | 1 |
| audit.FixedHLambdaReplacementOuterRegression | 7 | 5 | 2 |

All 68 declaration types and values have transitive axiom closure contained in
`propext`, `Classical.choice`, and `Quot.sound`. The separate pinned audit checks
every defining-module/name pair, complete elaborated type fingerprint, and
universe parameter list. The Python verifier additionally compares SHA256 of
each full pretty type, raw type expression, and direct-reference set; exact
axiom sets and explicit/generated classification are also pinned. Full type and
reference text remains in the private audit log, not duplicated into public
metadata.

There are 6,053 ordered imported modules, including 286 repository modules.
All 281 borrowed repository-module sources match successful baseline receipts;
the remaining five are the three fresh bridge modules and two fresh prerequisites.
The ordered imported union is hashed, and all repository source hashes are
published in `dependency-sources.json`. These records attest source consistency,
not a rebuild of the whole dependency graph.

## Scope

For every fixed `c>0`, the literal actual Λ satisfies the stated relative and
absolute product replacement uniformly in `D,j,n`, with witness
`C=384π exp(1)` and `D₀` chosen before `D,j,n`. The proof covers `n=1`, `p=2`, all
three shifts, and the inclusive upper log window.

The outer theorem propagates that error through the actual character norm and
totient weights, bounded complex `K` on the original closed window, and literal
`LDerivAtOne χ` scalar. It proves error at most
`C L⁴(1+log B)²/B²` for `B=log P=L⁹`, uniformly in `χ,j,K` after `C,D₀` are chosen.
It needs no assumption (A), and no approximation hypothesis for Λ or the
arithmetic main term. The baseline arithmetic asymptotic, complex Abel step,
and final `m_H` result remain outside this package.

See `INDEPENDENT_SCOPE_REVIEW.md` for the prime estimate, prime-sum split,
finite-product exponential argument, uniformity, scalar bound, and endpoint review.

## Source provenance

The original three sources are byte-identical to export
`ee25d49b114f629de3d53438a1f9cdf1481ac4b3`, based on
`3203236c046a128ecaedbefffb41ab1fce539f6d`. The two outer sources are byte-identical
to `c70847bc90d838b0ce10d0e86f6dcf0c1d0600a7`, whose exported parent is the original
commit. The applied checkout HEAD during review was
`12035d10c535c038c76e82b1cefc11bc837cb0a8`; its unrelated pending work was untouched.
Commit provenance comes from the supplied export manifests; source bytes were
independently verified. This package is integrity evidence, not a signature.

## Verify a complete private audit log

From either the standalone package or the same files installed in the repository:

```sh
python audit/lambda_replacement/verify_evidence.py /path/to/inventory.log \
  --repo-root /path/to/applied/repository
```

Omit `--repo-root` to check the package and log alone. The verifier touches only
the explicitly declared package files, the bounded evidence directory, and the
listed dependency paths. It never walks the containing repository. Every public
file is UTF-8 and at most 150,000 bytes. `SHA256SUMS` covers the exact declared
package file set and permits unrelated files elsewhere in an installed checkout.

## Reproduce independently

```sh
python audit/lambda_replacement/reproduce.py \
  --repo-root /path/to/applied/repository \
  --work-dir /path/to/new/private/directory \
  --lean /path/to/lean-4.30.0/bin/lean \
  --base-lean-path "$READONLY_LEAN_PATH" \
  --lock-file /path/to/shared/private-lean.lock
```

Use the same lock as other workers. Dependency packages and immutable compiled
objects must already be present. The harness reserves all fresh output suffixes,
builds the two prerequisites and three bridge files, runs both original regression
audits (12 named lemmas), and runs the complete pinned inventory. It finishes by
calling the bounded verifier against the new full log. Output files, logs and
receipts remain in the private work directory.
