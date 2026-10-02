import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
Exact source transcription and calculus for arXiv:2211.02515, equations (8.13)--(8.24).
The source is SHA256 5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b.
All decimal parameters are represented by exact rationals.
-/

set_option autoImplicit false
noncomputable section
open Complex intervalIntegral
namespace Section8

abbrev p : ℂ := (Real.pi : ℂ)
abbrev I : ℂ := Complex.I

def f16 (z : ℝ) : ℂ := (1 + p * I / 2 * z) * exp (3 * p * I / 2 * z)
def f26 (z : ℝ) : ℂ := (1 - p * I / 2 * z) * exp (3 * p * I / 2 * z)
def f36 (z : ℝ) : ℂ := (1 - 3 * p * I / 2 * z) * exp (3 * p * I / 2 * z)
def f17 (z : ℝ) : ℂ := (1 + 3 * p * I / 2 * z) * exp (5 * p * I / 2 * z)
def f27 (z : ℝ) : ℂ := (1 + p * I / 2 * z) * exp (5 * p * I / 2 * z)
def f37 (z : ℝ) : ℂ := (1 - p * I / 2 * z) * exp (5 * p * I / 2 * z)
def g16 (z : ℝ) : ℂ := 8/3 + (-5/3 - p * I / 2 * z) * exp (-3 * p * I / 2 * z)
def g26 (z : ℝ) : ℂ := 4/3 + (-1/3 + p * I / 2 * z) * exp (-3 * p * I / 2 * z)
def g36 (z : ℝ) : ℂ := 8/9 + (1/9 + p * I / 6 * z) * exp (-3 * p * I / 2 * z)
def g17 (z : ℝ) : ℂ := 24/25 + (1/25 + p * I / 10 * z) * exp (-5 * p * I / 2 * z)
def g27 (z : ℝ) : ℂ := 12/25 + (13/25 + 3 * p * I / 10 * z) * exp (-5 * p * I / 2 * z)
def g37 (z : ℝ) : ℂ := 8/25 + (17/25 - 3 * p * I / 10 * z) * exp (-5 * p * I / 2 * z)

def h11 (z : ℝ) : ℂ := 1/2*f16 z*g16 z + 2*f26 z*g26 z + 3/2*f36 z*g36 z
def h22 (z : ℝ) : ℂ := 1/2*f17 z*g17 z + 2*f27 z*g27 z + 3/2*f37 z*g37 z
def h21 (z : ℝ) : ℂ := 1/2*f17 z*g16 (z+1/250) + 2*f27 z*g26 (z+1/250) + 3/2*f37 z*g36 (z+1/250)
def h12 (z : ℝ) : ℂ := 1/2*f16 (z+1/250)*g17 z + 2*f26 (z+1/250)*g27 z + 3/2*f36 (z+1/250)*g37 z

def b11 : ℂ := 1 / ((63/125)^2*p) * ∫ z in (0:ℝ)..(63/125), h11 z
def b22 : ℂ := 1 / ((1/2)^2*p) * ∫ z in (0:ℝ)..(1/2), h22 z
def b21 : ℂ := 1 / ((63/125)*(1/2)*p) * ∫ z in (0:ℝ)..(1/2), h21 z
def b12 : ℂ := 1 / ((63/125)*(1/2)*p) * ∫ z in (0:ℝ)..(1/2), h12 z

def c11 : ℂ := b11 + star b11
def c22 : ℂ := b22 + star b22
def c12 : ℂ := b12 + star b21
def c21 : ℂ := star c12
def iota2 : ℂ := 94977/100000 - 138995/100000*I
def c1 : ℂ := c11 + iota2*c21 + star iota2*c12 + (‖iota2‖^2:ℝ)*c22

def pe (A B C k : ℂ) (z : ℝ) : ℂ :=
  (A + B*z + C*(z:ℂ)^2) * exp (k*z)
def pePrimitive (A B C k : ℂ) (z : ℝ) : ℂ :=
  exp (k*z) * (A/k + B*((z:ℂ)/k - 1/k^2) +
    C*((z:ℂ)^2/k - 2*z/k^2 + 2/k^3))

theorem pePrimitive_hasDerivAt (A B C k : ℂ) (hk : k ≠ 0) (z : ℝ) :
    HasDerivAt (pePrimitive A B C k) (pe A B C k z) z := by
  have hp : HasDerivAt (fun w : ℂ =>
      A/k + B*(w/k - 1/k^2) + C*(w^2/k - 2*w/k^2 + 2/k^3))
      (B/k + C*(2*(z:ℂ)/k - 2/k^2)) (z:ℂ) := by
    convert ((hasDerivAt_const (z:ℂ) (A/k)).add
      ((((hasDerivAt_id (z:ℂ)).div_const k).sub_const (1/k^2)).const_mul B)).add
      ((((((hasDerivAt_id (z:ℂ)).pow 2).div_const k).sub
        (((hasDerivAt_id (z:ℂ)).const_mul 2).div_const (k^2))).add_const (2/k^3)).const_mul C) using 1
    dsimp
    ring
  have he : HasDerivAt (fun w : ℂ => exp (k*w)) (exp (k*(z:ℂ))*k) (z:ℂ) := by
    simpa using (Complex.hasDerivAt_exp (k*(z:ℂ))).comp (z:ℂ)
      ((hasDerivAt_id (z:ℂ)).const_mul k)
  have h : HasDerivAt (fun w : ℂ =>
      exp (k*w) * (A/k + B*(w/k - 1/k^2) + C*(w^2/k - 2*w/k^2 + 2/k^3)))
      (pe A B C k z) (z:ℂ) := by
    convert he.mul hp using 1
    dsimp [pe]
    field_simp
    ring
  exact h.comp_ofReal

theorem integral_pe (A B C k : ℂ) (hk : k ≠ 0) (a b : ℝ) :
    (∫ z in a..b, pe A B C k z) = pePrimitive A B C k b - pePrimitive A B C k a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro z _
    exact pePrimitive_hasDerivAt A B C k hk z
  · exact (by unfold pe; fun_prop : Continuous (pe A B C k)).intervalIntegrable a b

end Section8
