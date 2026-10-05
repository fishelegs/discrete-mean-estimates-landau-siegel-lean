# Draft finite V4 estimates and balanced core identities

Research checkpoint dated 2026-10-05, originally based on public repository commit `1b1bdae9503bf45acc091381e5574b86930f55ae`; this increment is based on published draft checkpoint `3da60fca87a0eaf64e425f34281059966c66dc9b`.

Status: ten mathematical notes have passed independent source review at the specific scopes below. The Gaussian-target results pay finite reduced principal corrections, directly prove the weighted equality row, and localize the actual swapped cross to its unequal near band, pay all four actual integer-ratio diagonals, and reduce a sufficient positive-energy strategy to one still-unproved near aggregate upper bound. The smooth-target result pays a sub-64 norm reduction and one entire transformed equality row at its stated scope. The smaller-inverse result has explicit attachment limits; the four-branch result proves exact identities only. None of these new notes has been formalized in Lean. The full original moment and final strict gap remain OPEN. No new Lean source is added by this checkpoint.

## Mathematical results

Keep the original assumption `0 < L(1,chi) < (log D)^(-2022)` and the original target exponent 2024. Set `L=log D`, `B=log P=L^9`, `X=D^4`, `R=P/D^8`, and `S=P/D^14`.

1. [Reciprocal product](01_reciprocal_product.md): for each fixed `c>0`, uniformly at `s=1+c/L^9+iv`, `|v|<=L^5`, the reciprocal `1/(zeta(s)L(s,chi))` is `O(L log L)`. This uses the specified public quantitative Deuring–Heilbronn and reciprocal-zeta theorems.
2. [First actual finite-V4 sector](02_short_sector.md): the finite tuple region `r=d*m<=R`, with output `d*m*n<=M<=P^2 D^5`, has original positive family/Gaussian energy `O(P^2 L^(958/15)(log L)^(42/5))`.
3. [Second actual finite-V4 sector](03_small_product_sector.md): the disjoint region `r=d*m>R`, `n=n2*n3<=S`, with the same output cap, has energy `O(P^2 L^(958/15)(log L)^(52/5))`.

4. [Smaller arithmetic inverse tail](04_smaller_inverse_tail.md): every fixed `delta>1` gives `sum_(D^delta<n<=P^3)nu(n)^2/n = O_delta(L^-2011)`, improved to `L^-2019` when the upper endpoint is `D^4`. The actual discarded-sector and cross estimates still retain a `D^5` loss at the full core, so this does not replace the original inverse cutoff globally.
5. [Exact balanced four-branch identity](05_balanced_four_branch_identity.md): the original integer masks, root numbers, four head/dual branches, all six signed cross kernels, shifted equality-row arithmetic, and phase identities are explicit. This supplies no new positive-energy estimate or signed gain.

6. [Smooth balanced reduction and actual weighted equality row](06_smooth_balanced_diagonal.md): a fixed-profile infinite smooth target differs from the hard balanced core by squared norm `O(P^2 L^(958/15)(log L)^(52/5))`, hence `O(P^2 L^(959/15))`. The infinite output/input extensions are paid. For this new target's actual `W10*conjugate(W01)` cross, the entire integer-equality row `e*m*m'=D*d*n*n'`, including its restricted even-principal subtraction, has absolute contribution `O(P^2 tau_6(D)D^(-1/2)L^228(log L)^6)=o(P^2)`. All Mellin heights and all dual indices are included.

7. [Gaussian-log reduction and principal corrections](07_gaussian_principal_mean.md): the original hard balanced core and the literal infinite Gaussian-log target differ by squared family norm `O(P^2 L^(958/15)(log L)^(52/5))`, hence `O(P^2 L^(959/15))`, with paid input/output extensions. Each of its four exact artificial-AFE principal-p-unit branches is `O(D^6 L^6400)`. Every correctly reduced finite even-principal root-kernel correction is therefore `O(P D^12 L^12800)=o(P^2)`. For the swapped cross, the equality-restricted principal part is `O(P tau_6(D)D^(-1/2)L^228(log L)^6)`, and its complementary principal mean is paid by exact subtraction. The full-kernel Gaussian-target integer-equality row is directly re-established as `O(P^2 tau_6(D)D^(-1/2)L^228(log L)^6)=o(P^2)` for the Gaussian weights.

8. [Actual swapped-cross time localization](08_swap_time_localization.md): for the literal Gaussian-target swapped cross, the part with `|log(e*m*m'/(D*d*n*n'))|>L^-395` is `O_K(P^-18)`. For every fixed `A>0`, a sufficiently large fixed AFE decay order gives `O_(A,K)(P^-A)`; `K` is the fixed shift bound and thresholds may depend on `A,K`. All ten Mellin coordinates, infinite AFE tails, both sharp time-window endpoints and the original finite inverse are retained. Exact total-minus-far-minus-equality bookkeeping leaves only the signed geometrical kernel on the unequal near band, with both congruence signs still explicit and unbounded.

9. [All four actual integer-ratio diagonals](09_four_branch_diagonals.md): each Gaussian AFE branch's full nonprincipal parity-kernel integer-ratio row satisfies `0<=D_ij<<P^2(log L)^6`; their sum does too. The actual shifted Euler bound is `sum a(k)^2/k^(1+1/B)<<L^68`, with `a=|upsilon|*|nu_beta|*tau_2`, ramification and all prime powers retained. One global Rankin factor attaches all-height weights before the literal prime-window width cancels `L^68`. Each restricted even-principal row is `O(P(log L)^6)`, and its complementary mean is paid by total minus equality. Unequal ordinary congruence rows and complete positive branch norms remain open.

10. [Four near parity correlations as a sufficient target](10_near_parity_sufficient_gate.md): each same-branch full-kernel far part `|log(Y_ij/X_ij)|>L^-395` is `O(P^-18)`, after exact same-pair conductor cancellation and control of all residual gamma phases. The exact aggregate reduction is `sum ||B_ij||_H^2 = Re sum N_ij + O(P^2(log L)^6)`, where `N_ij` retains both ordinary parity congruences on the unequal near band. A single one-sided bound `Re sum N_ij <= C_b P^2 L^b` for some fixed `b<64` would suffice, by pointwise unit-root Cauchy and the accepted norm transfers, for exponent `max(b,1,959/15)<64`. That arithmetic upper bound is unproved. This condition is sufficient, not necessary, and is not identified with the original signed half-threshold.

Both sector estimates imply `O(P^2 L^(959/15))`, where `959/15<64`. Original finite inverse `d<=D^4`, four-gamma `V4(m*n)`, imaginary shifts, both character parities, narrow prime window, restricted Gaussian, p-unit zeros, and exact nonprincipal projection are retained.

The sectors are disjoint as finite tuple sets, but need not be orthogonal as sampled polynomials. Cauchy bounds their mutual cross; the norm triangle inequality pays their union with the same fixed exponent.

## What remains open

Within the retained core, the remaining exact region is

    r>P/D^8, n>P/D^14, rn<=M, d<=D^4,
    r<=P D^19, n<=P D^13.

Its energy and joint cross with the paid union remain open, as does the final theorem assembly. The compact-profile and Gaussian-log norm reductions transfer existence of a fixed sub-64 positive norm bound by triangle; neither gives an `o(P^2)` squared-moment identity or pays a transition cross with the unknown balanced norm. Their weights and individual cross rows are not identified with each other or the earlier integer-cell bump-train weights. The Gaussian result pays its complementary swapped even-principal mean and all other correctly reduced finite principal corrections; it does not transfer that principal result termwise to the compact-profile target. For the Gaussian target, the swapped cross is now reduced to unequal near-band positive and negative congruences; those residuals, the other nonzero congruence rows, the oscillatory parts of the other five signed crosses, and all four complete positive branch norms beyond the paid integer-ratio diagonals and principal corrections remain open. The four same-branch ordinary congruence rows are now localized to their unequal near bands. One upper bound on their aggregate real part would be sufficient for the positive-energy strategy; it has not been proved. This strategy would avoid needing separate bounds for the other Gauss-root crosses, but establishes none of them. A same-output diagonal is never substituted for the full positive quadratic form. No full finite-G moment, final numerical inequality, or Landau–Siegel contradiction follows yet.

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
- [Finite diagnostics](diagnostics/README.md) include the original mathematical scripts and expected results for both sectors, the smaller-inverse tail, the four-branch identity, the smooth balanced reduction, the Gaussian principal calculation, swapped-cross localization, all four integer-ratio diagonals, and the sufficient near-aggregate reduction, with no claim that numerical tests certify asymptotics
- [Checkpoint verifier](verify_checkpoint.py) checks all listed file bytes and exact rational exponent bookkeeping
- [Publication manifest](PUBLICATION_MANIFEST.json) lists the complete added payload with SHA-256 values and validation labels

The proofs retain accepted upstream tail and large-sieve interfaces at their stated scope. Their source hashes are identified; this checkpoint does not claim a fresh recursive proof or Lean dependency audit of every upstream interface. External primary papers are cited by versioned links, not redistributed.

## Checkpoint discipline

Create another draft checkpoint after a finished verified mathematical result, a meaningful proof revision, or a change in validation status. Preserve incomplete work with an explicit DRAFT or UNVERIFIED label; use SOURCE_REVIEWED or LEAN_VERIFIED only for the scope actually checked.

A local Git commit alone is not an off-machine backup. A checkpoint becomes remotely backed up only after the independent draft branch and exact remote commit have been verified. Publishing a draft does not merge it into the main branch or certify its mathematics.
