# Draft finite V4 estimates and balanced core identities

Research checkpoint dated 2026-10-05, originally based on public repository commit `1b1bdae9503bf45acc091381e5574b86930f55ae`; this increment is based on draft checkpoint `357c5c396342d4f0fde6d404e96907b42c85f98e`.

Status: seven mathematical notes have passed independent source review at the specific scopes below. The Gaussian-target result pays its finite reduced principal corrections and directly reproves its weighted equality row. The smooth-target result pays a sub-64 norm reduction and one entire transformed equality row at its stated scope. The smaller-inverse result has explicit attachment limits; the four-branch result proves exact identities only. None of these new notes has been formalized in Lean. The full original moment and final strict gap remain OPEN. No new Lean source is added by this checkpoint.

## Mathematical results

Keep the original assumption `0 < L(1,chi) < (log D)^(-2022)` and the original target exponent 2024. Set `L=log D`, `B=log P=L^9`, `X=D^4`, `R=P/D^8`, and `S=P/D^14`.

1. [Reciprocal product](01_reciprocal_product.md): for each fixed `c>0`, uniformly at `s=1+c/L^9+iv`, `|v|<=L^5`, the reciprocal `1/(zeta(s)L(s,chi))` is `O(L log L)`. This uses the specified public quantitative Deuring–Heilbronn and reciprocal-zeta theorems.
2. [First actual finite-V4 sector](02_short_sector.md): the finite tuple region `r=d*m<=R`, with output `d*m*n<=M<=P^2 D^5`, has original positive family/Gaussian energy `O(P^2 L^(958/15)(log L)^(42/5))`.
3. [Second actual finite-V4 sector](03_small_product_sector.md): the disjoint region `r=d*m>R`, `n=n2*n3<=S`, with the same output cap, has energy `O(P^2 L^(958/15)(log L)^(52/5))`.

4. [Smaller arithmetic inverse tail](04_smaller_inverse_tail.md): every fixed `delta>1` gives `sum_(D^delta<n<=P^3)nu(n)^2/n = O_delta(L^-2011)`, improved to `L^-2019` when the upper endpoint is `D^4`. The actual discarded-sector and cross estimates still retain a `D^5` loss at the full core, so this does not replace the original inverse cutoff globally.
5. [Exact balanced four-branch identity](05_balanced_four_branch_identity.md): the original integer masks, root numbers, four head/dual branches, all six signed cross kernels, shifted equality-row arithmetic, and phase identities are explicit. This supplies no new positive-energy estimate or signed gain.

6. [Smooth balanced reduction and actual weighted equality row](06_smooth_balanced_diagonal.md): a fixed-profile infinite smooth target differs from the hard balanced core by squared norm `O(P^2 L^(958/15)(log L)^(52/5))`, hence `O(P^2 L^(959/15))`. The infinite output/input extensions are paid. For this new target's actual `W10*conjugate(W01)` cross, the entire integer-equality row `e*m*m'=D*d*n*n'`, including its restricted even-principal subtraction, has absolute contribution `O(P^2 tau_6(D)D^(-1/2)L^228(log L)^6)=o(P^2)`. All Mellin heights and all dual indices are included.

7. [Gaussian-log reduction and principal corrections](07_gaussian_principal_mean.md): the original hard balanced core and the literal infinite Gaussian-log target differ by squared family norm `O(P^2 L^(958/15)(log L)^(52/5))`, hence `O(P^2 L^(959/15))`, with paid input/output extensions. Each of its four exact artificial-AFE principal-p-unit branches is `O(D^6 L^6400)`. Every correctly reduced finite even-principal root-kernel correction is therefore `O(P D^12 L^12800)=o(P^2)`. For the swapped cross, the equality-restricted principal part is `O(P tau_6(D)D^(-1/2)L^228(log L)^6)`, and its complementary principal mean is paid by exact subtraction. The full-kernel Gaussian-target integer-equality row is directly re-established as `O(P^2 tau_6(D)D^(-1/2)L^228(log L)^6)=o(P^2)` for the Gaussian weights.

Both sector estimates imply `O(P^2 L^(959/15))`, where `959/15<64`. Original finite inverse `d<=D^4`, four-gamma `V4(m*n)`, imaginary shifts, both character parities, narrow prime window, restricted Gaussian, p-unit zeros, and exact nonprincipal projection are retained.

The sectors are disjoint as finite tuple sets, but need not be orthogonal as sampled polynomials. Cauchy bounds their mutual cross; the norm triangle inequality pays their union with the same fixed exponent.

## What remains open

Within the retained core, the remaining exact region is

    r>P/D^8, n>P/D^14, rn<=M, d<=D^4,
    r<=P D^19, n<=P D^13.

Its energy and joint cross with the paid union remain open, as does the final theorem assembly. The compact-profile and Gaussian-log norm reductions transfer existence of a fixed sub-64 positive norm bound by triangle; neither gives an `o(P^2)` squared-moment identity or pays a transition cross with the unknown balanced norm. Their weights and individual cross rows are not identified with each other or the earlier integer-cell bump-train weights. The Gaussian result pays its complementary swapped even-principal mean and all other correctly reduced finite principal corrections; it does not transfer that principal result termwise to the compact-profile target. For the Gaussian target, nonzero positive congruence shifts, negative congruence rows, the oscillatory parts of the other five signed crosses, and all four positive branch norms beyond their principal corrections remain open. A same-output diagonal is never substituted for the full positive quadratic form. No full finite-G moment, final numerical inequality, or Landau–Siegel contradiction follows yet.

### Scope reconciliation with the earlier remote output theorem

The original output beyond `M0=P^2D^5` is already paid globally by the separately accepted remote-output-tail theorem, including its cross with the entire core. Up to the original finite endpoint `Y=D^4P^3`, it gives

    B_remote << P^2 D^-7 L^24836,
    |C_core,remote| << P^2 D^-1 L^12244 log L = o(P^2),
    B_full = B_core(k<=P^2D^5) + o(P^2).

The exact earlier source and acceptance identities are pinned in SOURCE_PINS.json. That theorem retains the original finite inverse, input mask, four-gamma weight, shifts, prime/parity/projector conditions, Gaussian and every tail interaction. It is used here as an accepted upstream result, not reproved or redistributed.

The individual sector notes' statements that they do not pay the output complement describe their own proof scope. They do not reopen that already-paid global complement. The remaining core obligation is the balanced region's energy and joint cross, followed by final assembly.

The generic resonant example in the smaller-inverse note concerns arbitrary separable coefficients, conditional on a nonempty original prime window; it is not a lower bound or impossibility claim for the actual arithmetic coefficients. The four-branch note likewise gives no weighted-row sign or nonvanishing assertion and no energy gain.

## Evidence and reproduction

- [Exact source pins](SOURCE_PINS.json) distinguish original source identities from these edited publication documents and link the public primary references
- [Finite diagnostics](diagnostics/README.md) include the original mathematical scripts and expected results for both sectors, the smaller-inverse tail, the four-branch identity, the smooth balanced reduction, and the Gaussian principal calculation, with no claim that numerical tests certify asymptotics
- [Checkpoint verifier](verify_checkpoint.py) checks all listed file bytes and exact rational exponent bookkeeping
- [Publication manifest](PUBLICATION_MANIFEST.json) lists the complete added payload with SHA-256 values and validation labels

The proofs retain accepted upstream tail and large-sieve interfaces at their stated scope. Their source hashes are identified; this checkpoint does not claim a fresh recursive proof or Lean dependency audit of every upstream interface. External primary papers are cited by versioned links, not redistributed.

## Checkpoint discipline

Create another draft checkpoint after a finished verified mathematical result, a meaningful proof revision, or a change in validation status. Preserve incomplete work with an explicit DRAFT or UNVERIFIED label; use SOURCE_REVIEWED or LEAN_VERIFIED only for the scope actually checked.

A local Git commit alone is not an off-machine backup. A checkpoint becomes remotely backed up only after the independent draft branch and exact remote commit have been verified. Publishing a draft does not merge it into the main branch or certify its mathematics.
