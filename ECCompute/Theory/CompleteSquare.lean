/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The completing-the-square model isomorphism

Over `ℚ` (characteristic `≠ 2`) the substitution `y ↦ y - (a₁x + a₃)/2` (the change of variables
`⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩`) carries a general Weierstrass model `W` to a short model
`y² = x³ + a₂'x² + a₄'x + a₆'`, on which the descent character is stated. Rank is an isomorphism
invariant, so a rank lower bound on the short model transfers back; see `pointAddEquiv`.

The point-on-curve check `checkPoint`/`checkPoints` used alongside this isomorphism lives in
`ECCompute.Kernel`.

## Main results

* `CompleteSquare.completeSquare`, `CompleteSquare.shortModel`: the
  `⟨1, 0, -a₁/2, -a₃/2⟩` change of variables and the resulting short model
  `y² = x³ + a₂'x² + a₄'x + a₆'`.
* `CompleteSquare.pointAddEquiv`: this change of variables as a group isomorphism `W.Point ≃+
  (shortModel W).Point`, so a rank lower bound transfers between the two models.
-/

section

namespace ECCompute.CompleteSquare

open WeierstrassCurve

/-! ## The completing-the-square model isomorphism -/

/-- The change of variables `⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩` completing the square for a curve
`W`: the substitution `y ↦ y - (W.a₁ x + W.a₃)/2` (over `ℚ`, where `2` is invertible) that clears
the `a₁` and `a₃` coefficients. -/
def completeSquare (W : WeierstrassCurve ℚ) : VariableChange ℚ := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩

/-- The short model `y² = x³ + a₂'x² + a₄'x + a₆'` obtained from `W` by completing the square. Its
`a₁` and `a₃` coefficients vanish (`shortModel_a₁`, `shortModel_a₃`). -/
public def shortModel (W : WeierstrassCurve ℚ) : WeierstrassCurve ℚ := completeSquare W • W

variable {W : WeierstrassCurve ℚ}

@[simp]
public theorem shortModel_a₁ : (shortModel W).a₁ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₁]

@[simp]
public theorem shortModel_a₂ : (shortModel W).a₂ = W.a₂ + W.a₁ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₂, inv_one, Units.val_one, one_pow]

@[simp]
public theorem shortModel_a₃ : (shortModel W).a₃ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₃]

@[simp]
public theorem shortModel_a₄ : (shortModel W).a₄ = W.a₄ + W.a₁ * W.a₃ / 2 := by
  grind [shortModel, completeSquare, variableChange_a₄, inv_one, Units.val_one, one_pow]

@[simp]
public theorem shortModel_a₆ : (shortModel W).a₆ = W.a₆ + W.a₃ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₆, inv_one, Units.val_one, one_pow]

/-- A point `(x, y)` lies on the general model `W` iff `(x, y + (a₁x + a₃)/2)` lies on the short
model. -/
theorem equation_completeSquare {x y : ℚ} : W.toAffine.Equation x y ↔
      (shortModel W).toAffine.Equation x (y + (W.a₁ * x + W.a₃) / 2) := by
  rw [Affine.equation_iff, Affine.equation_iff]
  grind [shortModel_a₁, shortModel_a₂, shortModel_a₃, shortModel_a₄, shortModel_a₆]

section GroupIso

open WeierstrassCurve.Affine

/-- Elementary disjunction fact underlying the transfer of the nonsingular condition: the two
partial-derivative non-vanishing conditions on the general and short models are related by the
invertible substitution `(F_X, F_Y) ↦ (F_X - σ F_Y, F_Y)`. -/
theorem or_ne_zero_sub_iff {A B σ : ℚ} : (A ≠ 0 ∨ B ≠ 0) ↔ (A - σ * B ≠ 0 ∨ B ≠ 0) := by
  by_cases hB : B = 0 <;> simp [hB]

/-- Two affine points with equal coordinates are equal (nonsingularity proofs are irrelevant). -/
public theorem point_some_congr {C : WeierstrassCurve ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : C.toAffine.Nonsingular x₁ y₁} {h₂ : C.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : C.toAffine.Point) = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

/-- A point `(x, y)` is nonsingular on the general model `W` iff `(x, y + (a₁x + a₃)/2)` is
nonsingular on the short model. -/
theorem nonsingular_completeSquare {x y : ℚ} : W.toAffine.Nonsingular x y ↔
      (shortModel W).toAffine.Nonsingular x (y + (W.a₁ * x + W.a₃) / 2) := by
  rw [nonsingular_iff', nonsingular_iff', ← equation_completeSquare]
  refine and_congr_right fun _ ↦ ?_
  have e1 : (shortModel W).toAffine.a₁ * (y + (W.a₁ * x + W.a₃) / 2)
        - (3 * x ^ 2 + 2 * (shortModel W).toAffine.a₂ * x + (shortModel W).toAffine.a₄)
      = (W.toAffine.a₁ * y - (3 * x ^ 2 + 2 * W.toAffine.a₂ * x + W.toAffine.a₄))
        - W.a₁ / 2 * (2 * y + W.toAffine.a₁ * x + W.toAffine.a₃) := by
    grind [shortModel_a₁, shortModel_a₂, shortModel_a₄]
  have e2 : 2 * (y + (W.a₁ * x + W.a₃) / 2) + (shortModel W).toAffine.a₁ * x
        + (shortModel W).toAffine.a₃
      = 2 * y + W.toAffine.a₁ * x + W.toAffine.a₃ := by grind [shortModel_a₁, shortModel_a₃]
  rw [e1, e2]
  exact or_ne_zero_sub_iff

/-- The `Y`-negation commutes with the completing-the-square shift. -/
theorem negY_completeSquare {x y : ℚ} : (shortModel W).toAffine.negY x (y + (W.a₁ * x + W.a₃) / 2)
      = W.toAffine.negY x y + (W.a₁ * x + W.a₃) / 2 := by grind [negY, shortModel_a₁, shortModel_a₃]

/-- The `X`-coordinate of the sum is unchanged by the shift (the slope shifts by `a₁/2`). -/
theorem addX_completeSquare {x₁ x₂ ℓ : ℚ} : (shortModel W).toAffine.addX x₁ x₂ (ℓ + W.a₁ / 2)
      = W.toAffine.addX x₁ x₂ ℓ := by grind [addX, shortModel_a₁, shortModel_a₂]

/-- The `Y`-coordinate of the sum commutes with the shift. -/
theorem addY_completeSquare {x₁ x₂ y₁ ℓ : ℚ} :
    (shortModel W).toAffine.addY x₁ x₂ (y₁ + (W.a₁ * x₁ + W.a₃) / 2) (ℓ + W.a₁ / 2)
      = W.toAffine.addY x₁ x₂ y₁ ℓ
        + (W.a₁ * W.toAffine.addX x₁ x₂ ℓ + W.a₃) / 2 := by
  grind [addY, negY, negAddY, addX, shortModel_a₁, shortModel_a₂, shortModel_a₃]

/-- The slope commutes with the shift, up to the additive constant `a₁/2` coming from the
straightening of the tangent/secant line. Requires both points to lie on the general model and to be
in the non-degenerate branch of the addition law. -/
theorem slope_completeSquare {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (shortModel W).toAffine.slope x₁ x₂ (y₁ + (W.a₁ * x₁ + W.a₃) / 2) (y₂ + (W.a₁ * x₂ + W.a₃) / 2)
      = W.toAffine.slope x₁ x₂ y₁ y₂ + W.a₁ / 2 := by
  obtain rfl | hx := eq_or_ne x₁ x₂
  · have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    have hyeq : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyeq
    have hy' : y₁ + (W.a₁ * x₁ + W.a₃) / 2
        ≠ (shortModel W).toAffine.negY x₁ (y₁ + (W.a₁ * x₁ + W.a₃) / 2) := by
      rw [negY_completeSquare]
      intro hcontra
      exact hy (add_right_cancel hcontra)
    have hDval : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by grind [negY]
    have hDval' : (y₁ + (W.a₁ * x₁ + W.a₃) / 2)
          - (shortModel W).toAffine.negY x₁ (y₁ + (W.a₁ * x₁ + W.a₃) / 2)
        = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by grind [negY, shortModel_a₁, shortModel_a₃]
    have hden : 2 * y₁ + W.a₁ * x₁ + W.a₃ ≠ 0 := hDval ▸ sub_ne_zero.mpr hy
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, hDval, hDval', div_add' _ _ _ hden,
      div_eq_div_iff hden hden]
    grind [shortModel_a₁, shortModel_a₂, shortModel_a₄]
  · rw [slope_of_X_ne hx, slope_of_X_ne hx, div_add' _ _ _ (sub_ne_zero.mpr hx),
      div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hx)]
    grind

/-- Forward coordinate map on Mordell-Weil groups: `(x, y) ↦ (x, y + (a₁x + a₃)/2)`. -/
def fwd (W : WeierstrassCurve ℚ) : W.toAffine.Point → (shortModel W).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some x (y + (W.a₁ * x + W.a₃) / 2) (nonsingular_completeSquare.mp h)

/-- Inverse coordinate map: `(x, y) ↦ (x, y - (a₁x + a₃)/2)`. -/
def bwd (W : WeierstrassCurve ℚ) : (shortModel W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some x (y - (W.a₁ * x + W.a₃) / 2) (nonsingular_completeSquare.mpr (by simpa using h))

@[simp] theorem fwd_some {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    fwd W (.some x y h) = .some x (y + (W.a₁ * x + W.a₃) / 2) (nonsingular_completeSquare.mp h) :=
  rfl

@[simp] theorem bwd_some {x y : ℚ} (h : (shortModel W).toAffine.Nonsingular x y) :
    bwd W (.some x y h)
      = .some x (y - (W.a₁ * x + W.a₃) / 2) (nonsingular_completeSquare.mpr (by simpa using h)) :=
  rfl

/-- The forward map is additive: it commutes with the affine group law on both models. -/
theorem fwd_map_add (P Q : W.toAffine.Point) : fwd W (P + Q) = fwd W P + fwd W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hycond : y₁ + (W.a₁ * x₁ + W.a₃) / 2
        = (shortModel W).toAffine.negY x₂ (y₂ + (W.a₁ * x₂ + W.a₃) / 2) := by
      rw [negY_completeSquare, ← hy, hx]
    rw [Point.add_of_Y_eq hx hy, fwd_some, fwd_some, Point.add_of_Y_eq hx hycond]
    rfl
  · have hxy' : ¬(x₁ = x₂ ∧ y₁ + (W.a₁ * x₁ + W.a₃) / 2
        = (shortModel W).toAffine.negY x₂ (y₂ + (W.a₁ * x₂ + W.a₃) / 2)) := by
      rintro ⟨hx, hy⟩
      refine hxy ⟨hx, ?_⟩
      rw [negY_completeSquare, hx] at hy
      exact add_right_cancel hy
    have hℓ := slope_completeSquare h₁.left h₂.left hxy
    grind [Point.add_some, fwd_some, point_some_congr, addX_completeSquare, addY_completeSquare]

/-- The completing-the-square change of variables `y ↦ y + (a₁x + a₃)/2` induces a group
isomorphism between the Mordell-Weil groups of the general model `W` and the short model
`shortModel W`, so any rank lower bound on the short model transfers back. -/
public def pointAddEquiv (W : WeierstrassCurve ℚ) :
    W.toAffine.Point ≃+ (shortModel W).toAffine.Point :=
  AddEquiv.mk'
    ⟨fwd W, bwd W,
      fun P ↦ by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [fwd_some, bwd_some]; exact point_some_congr rfl (by grind),
      fun P ↦ by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [bwd_some, fwd_some]; exact point_some_congr rfl (by grind)⟩
    fwd_map_add

end GroupIso

end ECCompute.CompleteSquare

end
