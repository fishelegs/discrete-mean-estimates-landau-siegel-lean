# Migration Step 09 — genuine divisor-character coefficient

Step 09 replaces the legacy `nu_of_divisor_proved` placeholder with the actual
Dirichlet-character argument needed in Lemma 5.7.

## Mathematical content

For

`νχ(n) = ∑_{d ∣ n} χ(d)`

and `n ∣ D`, prove `νχ(n) = 1`.

If `d ∣ n` and `n ∣ D`, then `d ∣ D`.  For `d ≠ 1`, positivity of `D` rules out
`d = 0`, so `1 < d`.  Hence `d` and `D` are not coprime (`d` itself is a common
divisor greater than one).  By `ZMod.isUnit_iff_coprime`, `(d : ZMod D)` is not a
unit, and `MulChar.map_nonunit` gives `χ(d) = 0`.  The unique surviving divisor is
`d = 1`, where a character has value `1`.

## New trusted declarations

- `RealPrimitiveCharacter.evalNat_eq_zero_of_dvd_modulus`
- `divisorCharacterSum`
- `divisorCharacterSum_eq_one_of_dvd_modulus`
- `divisorCharacterSumReal`
- `divisorCharacterSumReal_eq_one_of_dvd_modulus`

## Status

This is source-level proof code against mathlib's actual APIs.  The current temporary
container still lacks a Lean toolchain, so kernel compilation remains pending.
