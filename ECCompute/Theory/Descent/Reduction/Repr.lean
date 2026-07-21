/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.IntModel
import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.ForMathlib.RatDenom
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# The integer projective representative of an affine point

For a point `P = (x, y)` on the rational curve `y² = x³ + a₂x² + a₄x + a₆`, the
denominator-is-a-square lemma gives `w : ℕ` with `x.den = w²` and `y.den = w³`, so that
`![x.num · w, y.num, w³] : Fin 3 → ℤ` is an integer projective representative of `P`.  This
file records it as `Trep x y w` together with the facts used to reduce it modulo `p`.

## Main declarations

* `ECCompute.Trep`: the integer representative `![x.num·w, y.num, w³]`.
* `ECCompute.Trep_map_ℚ`: over `ℚ`, `Trep x y w = w³ • [x : y : 1]`.
* `ECCompute.Trep_equation`: `Trep x y w` satisfies the projective equation of `curveℤ`.
* `ECCompute.Trep_nonsingular`: `Trep x y w` is a nonsingular projective point of `curveℤ`.
* `ECCompute.Trep_primitive`: `y.num` and `w³` are coprime.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ)

/-- The integer projective representative `![x.num · w, y.num, w³]` of the affine point
`(x, y)`, where `w` is the square-root witness of the denominators (`x.den = w²`, `y.den = w³`).
Over `ℚ` this is `w³ • [x : y : 1]` (see `Trep_map_ℚ`). -/
def Trep (x y : ℚ) (w : ℕ) : Fin 3 → ℤ := ![x.num * w, y.num, (w : ℤ) ^ 3]

/-- The image of `curveℤ` under `ℤ → ℚ`, in projective form, is the rational curve. -/
private theorem map_curveℤ_toProjective :
    (curveℤ a₂ a₄ a₆).toProjective.map (Int.castRingHom ℚ) = (curve a₂ a₄ a₆).toProjective := by
  change (curveℤ a₂ a₄ a₆).map (Int.castRingHom ℚ) = curve a₂ a₄ a₆
  rw [← baseChange_curveℤ_ℚ, WeierstrassCurve.baseChange, algebraMap_int_eq]

variable {x y : ℚ} {w : ℕ}

/-- Over `ℚ`, the integer representative equals `w³ • [x : y : 1]`. -/
theorem Trep_map_ℚ (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (Int.castRingHom ℚ) ∘ Trep x y w = (w : ℚ) ^ 3 • ![x, y, 1] := by
  have hx : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * (y.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  have e0 : (Int.castRingHom ℚ) (x.num * (w : ℤ)) = (w : ℚ) ^ 3 * x := by
    rw [eq_intCast]; push_cast; rw [hx, hden]; push_cast; grind
  have e1 : (Int.castRingHom ℚ) (y.num) = (w : ℚ) ^ 3 * y := by
    rw [eq_intCast, hy, hden']; grind
  have e2 : (Int.castRingHom ℚ) ((w : ℤ) ^ 3) = (w : ℚ) ^ 3 * 1 := by
    rw [eq_intCast]; push_cast; grind
  simp only [Trep]
  rw [Projective.comp_fin3, Projective.smul_fin3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [e0, e1, e2]

/-- The integer representative lies on the integral projective curve. -/
theorem Trep_equation (h : (curve a₂ a₄ a₆).toAffine.Equation x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curveℤ a₂ a₄ a₆).toProjective.Equation (Trep x y w) := by
  have hw : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.ne_zero_of_den_eq_pow two_ne_zero hden)
  rw [← Projective.map_equation (W' := (curveℤ a₂ a₄ a₆).toProjective)
      (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int, Trep_map_ℚ hden hden',
    Projective.equation_smul _ (isUnit_iff_ne_zero.2 (pow_ne_zero 3 hw)),
    Projective.equation_some, map_curveℤ_toProjective]
  exact h

/-- The integer representative is a nonsingular projective point of the integral curve. -/
theorem Trep_nonsingular (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curveℤ a₂ a₄ a₆).toProjective.Nonsingular (Trep x y w) := by
  have hw : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.ne_zero_of_den_eq_pow two_ne_zero hden)
  rw [← Projective.map_nonsingular (W' := (curveℤ a₂ a₄ a₆).toProjective)
      (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int, Trep_map_ℚ hden hden',
    Projective.nonsingular_smul _ (isUnit_iff_ne_zero.2 (pow_ne_zero 3 hw)),
    Projective.nonsingular_some, map_curveℤ_toProjective]
  exact h

/-- The `y`- and `z`-coordinates of the representative are coprime; in particular the
representative is primitive. -/
theorem Trep_primitive (hden' : y.den = w ^ 3) : IsCoprime (y.num) ((w : ℤ) ^ 3) := by
  have : IsCoprime (y.num) (y.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using y.reduced
  rwa [hden', Nat.cast_pow] at this

end ECCompute
