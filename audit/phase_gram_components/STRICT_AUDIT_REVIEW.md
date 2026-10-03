# Strict audit review

The scanner still exits 1: its 445 historical/structural candidates are not silently suppressed. Relative to the published Proposition2.6 baseline, exactly one candidate is new.

`ActualGramPiCollapse.lean:115`, `exact hcast`, closes a local cast of the proved library totient identity. The proof constructs `hcast` from `Nat.totient_mul_prod_primeFactors n`, pushes casts, and proves the prime-factor predecessor casts using primality. It is not an assumed target and introduces no Gram/norm premise. The new candidate is reviewed with no unresolved new concern.
