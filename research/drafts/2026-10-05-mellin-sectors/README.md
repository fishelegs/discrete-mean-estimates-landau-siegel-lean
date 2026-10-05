# Draft reciprocal estimate and two finite V4 sectors

Research checkpoint dated 2026-10-05, based on public repository commit `1b1bdae9503bf45acc091381e5574b86930f55ae`.

Status: the three analytic arguments passed independent source-proof review. They have not been formalized in Lean. The full original moment and final strict gap remain OPEN. No new Lean source is added by this checkpoint.

## Mathematical results

Keep the original assumption `0 < L(1,chi) < (log D)^(-2022)` and the original target exponent 2024. Set `L=log D`, `B=log P=L^9`, `X=D^4`, `R=P/D^8`, and `S=P/D^14`.

1. [Reciprocal product](01_reciprocal_product.md): for each fixed `c>0`, uniformly at `s=1+c/L^9+iv`, `|v|<=L^5`, the reciprocal `1/(zeta(s)L(s,chi))` is `O(L log L)`. This uses the specified public quantitative Deuring–Heilbronn and reciprocal-zeta theorems.
2. [First actual finite-V4 sector](02_short_sector.md): the finite tuple region `r=d*m<=R`, with output `d*m*n<=M<=P^2 D^5`, has original positive family/Gaussian energy `O(P^2 L^(958/15)(log L)^(42/5))`.
3. [Second actual finite-V4 sector](03_small_product_sector.md): the disjoint region `r=d*m>R`, `n=n2*n3<=S`, with the same output cap, has energy `O(P^2 L^(958/15)(log L)^(52/5))`.

Both sector estimates imply `O(P^2 L^(959/15))`, where `959/15<64`. Original finite inverse `d<=D^4`, four-gamma `V4(m*n)`, imaginary shifts, both character parities, narrow prime window, restricted Gaussian, p-unit zeros, and exact nonprincipal projection are retained.

The sectors are disjoint as finite tuple sets, but need not be orthogonal as sampled polynomials. Cauchy bounds their mutual cross; the norm triangle inequality pays their union with the same fixed exponent.

## What remains open

Within the retained core, the remaining exact region is

    r>P/D^8, n>P/D^14, rn<=M, d<=D^4,
    r<=P D^19, n<=P D^13.

Its energy and its crosses with the paid union are unproved here. The original output complement and its crosses are not paid by these notes. A same-output diagonal is never substituted for the full positive quadratic form. No full finite-G moment, final numerical inequality, or Landau–Siegel contradiction follows yet.

The first-sector note describes the obligations left by that theorem alone. The second-sector note and this overview give the later combined scope.

## Evidence and reproduction

- [Exact source pins](SOURCE_PINS.json) distinguish original source identities from these edited publication documents and link the public primary references
- [Finite diagnostics](diagnostics/README.md) include the original mathematical scripts and expected results, with no claim that numerical tests certify asymptotics
- [Checkpoint verifier](verify_checkpoint.py) checks all listed file bytes and exact rational exponent bookkeeping
- [Publication manifest](PUBLICATION_MANIFEST.json) lists the complete added payload with SHA-256 values and validation labels

The proofs retain accepted upstream tail and large-sieve interfaces at their stated scope. Their source hashes are identified; this checkpoint does not claim a fresh recursive proof or Lean dependency audit of every upstream interface. External primary papers are cited by versioned links, not redistributed.

## Checkpoint discipline

Create another draft checkpoint after a finished verified mathematical result, a meaningful proof revision, or a change in validation status. Preserve incomplete work with an explicit DRAFT or UNVERIFIED label; use SOURCE_REVIEWED or LEAN_VERIFIED only for the scope actually checked.

A local Git commit alone is not an off-machine backup. A checkpoint becomes remotely backed up only after the independent draft branch and exact remote commit have been verified. Publishing a draft does not merge it into the main branch or certify its mathematics.
