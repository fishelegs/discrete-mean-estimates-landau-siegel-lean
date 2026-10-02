# Lemma 12.1 final staged status (2026-10-02)

This supersedes only the unfinished-low-branch status in the historical high-stage CLOUD_LEMMA121_SOURCE_AUDIT.md. The source audit, high-stage statements, and all eight previously frozen module hashes are unchanged.

## Primary result: all three concrete actual branches

`lemma121_concrete_exact_proved : Lemma121ConcreteExactTarget` is kernel checked. One absolute positive C and kappa=1/2 are chosen before the original shared fixed positive c′; one threshold D0(c′) then works for every actual real primitive chi satisfying (A), every j=1,2,3 and every positive natural d in the relevant original ranges:

1. d<=P''1/T: |S_j(d)|<=C*T^(−1/2)
2. P''1/T<d<=P''1: |S_j(d)|<=C*L^(−7)
3. P''1<d<P2: |S_j(d)−S_exact_j(d)|<=C*L^(−15)

Here S is the actual original strict κ13 shifted character sum, and

  S_exact_j(d)=(L′(1,chi)/log P1) exp(−beta6 log(d/P''1))
                * (−1+(beta6−beta_j)log(d/P''1)).

The preferred high-range result retains this exact phase. It is precisely the main expression before the source's unsupported final linearization.

## Original and repaired status must remain distinct

- The original first branch is fully proved, with explicit bound 36*T^(−1/2); it in fact does not need (A). Public capstone: `lemma121_low_proved`.
- The transition has the complete concrete L^(−7) estimate. Public capstone: `lemma121_transition_proved`. The source's undefined alpha1 has NOT been silently assigned a meaning. If alpha1 is later independently resolved, its comparison with L^(−7) must be audited.
- The entire original high range has the proved exact-phase O(L^(−15)) replacement. Public capstone: `lemma121_exact_high_proved`.
- The optional alternative `lemma121_repaired_high_proved` uses the original linear phase with explicitly changed normalized error |epsilon|<10^(−3), not the printed 10^(−5). Its downstream numerical impact is unassessed. Do not imply that this 100-fold relaxation preserves later numerical inequalities.
- `Lemma121PrintedTarget` and `Lemma121PrintedHighTarget` remain frozen, UNPROVED propositions. No `lemma121_proved` theorem is introduced. Original Lemma 12.1 must not be marked completed as printed.
- The checked pure-phase lower bound in `lemma121_limiting_phase_exceeds_printed_budget` identifies a failure of the source proof's displayed phase budget. It is not an actual character counterexample under (A).

## New low/transition proof components

- `Lemma121LowBridge`: exact all-range finite identity. The lower weighted polynomial restores the strict lower support, while the strict upper polynomial preserves the nonzero upper endpoint correction.
- `Lemma121Low`: cancellation of the actual analytic Abel main terms, actual 4D/x and 16D/x tails, exponential absorption, complete original first branch.
- `Lemma121UniformPolynomial`: actual general Re(s)=1 weighted-polynomial bounds on 1<=x<P, using trivial bounds below D and local analytic/Abel bounds above D. The proof adapts the genuine generalizable bounds used by Lemma 10.1, but imports no staged Lemma 10.1 module and modifies no such files.
- `Lemma121Transition`: original endpoint geometry and actual L^(−7) transition estimate.
- `Lemma121Concrete`: one common-constant, common-threshold combination of all three concrete branches.

No contour hypotheses, result-shaped unproved analytic inputs, sorry/admit/custom axioms, changes to the character, or altered rational endpoints occur in the capstones. Algebraic estimate-composition lemmas have their hypotheses discharged by actual theorems in the final capstones.

## Repository validation

Thirteen production modules are promoted byte-for-byte to ZhangLS/Spec. High/low semantic regressions and all public axiom commands are combined into audit/CloudLemma121ConcreteRegression.lean. Central validation and reproducible commands are recorded in CLOUD_LEMMA121_CONCRETE_STATUS.md.
