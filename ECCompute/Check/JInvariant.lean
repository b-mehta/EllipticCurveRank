/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.ModelIso
import ECCompute.QuickRfl

/-!
# Certifying the j-invariant

The j-invariant `j = c₄³ / Δ` is an isomorphism invariant: it is the same for every Weierstrass
model of a curve (mathlib's `WeierstrassCurve.variableChange_j`), so it can be read off any integral
model `⟨a₁, …, a₆⟩` with no minimal model needed.

`j_eq_iff` reduces a claim `j = q` to the polynomial identity `c₄³ = Δ · q`, avoiding division; the
per-curve obligation is then the kernel-reducible `Bool` check `(c₄³ == Δ · q) = true` (`j_eq_of_beq`).
-/

namespace ECCompute

open WeierstrassCurve

/-- For a Weierstrass curve with invertible discriminant, `j = q` iff `c₄³ = Δ · q`. -/
theorem j_eq_iff (W : WeierstrassCurve ℚ) [W.IsElliptic] (q : ℚ) :
    W.j = q ↔ W.c₄ ^ 3 = W.Δ * q := by
  rw [WeierstrassCurve.j, Units.inv_mul_eq_iff_eq_mul, coe_Δ']

/-- Over `ℚ`, a nonzero discriminant makes a model an elliptic curve (so `j` is defined). -/
theorem isElliptic_of_Δ_ne_zero {W : WeierstrassCurve ℚ} (hΔ : W.Δ ≠ 0) : W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr hΔ⟩

/-- `IsElliptic` from a kernel-reducible `Bool` witness `(Δ != 0) = true`. -/
theorem isElliptic_of_bne {W : WeierstrassCurve ℚ} (h : (W.Δ != 0) = true) : W.IsElliptic :=
  isElliptic_of_Δ_ne_zero (by simpa using h)

/-- `j = q` from a kernel-reducible `Bool` witness `(c₄³ == Δ · q) = true` (discharged by
`quickRfl`, i.e. `reflBoolTrue`, as elsewhere in the project) -- no `norm_num`. -/
theorem j_eq_of_beq (W : WeierstrassCurve ℚ) [W.IsElliptic] (q : ℚ)
    (h : (W.c₄ ^ 3 == W.Δ * q) = true) : W.j = q :=
  (j_eq_iff W q).mpr (eq_of_beq h)

/-- The example curve `y² = x³ - 82x` (the `CurveThirteen` deliverable) is elliptic; declaring the
instance makes `.j` well-formed for the curve. -/
instance : (⟨0, 0, 0, -82, 0⟩ : WeierstrassCurve ℚ).IsElliptic := isElliptic_of_bne (by quickRfl)

/-- Worked example: `y² = x³ - 82x` has `j = 1728`, via the kernel `Bool` check `c₄³ == Δ · 1728`. -/
example : (⟨0, 0, 0, -82, 0⟩ : WeierstrassCurve ℚ).j = 1728 := j_eq_of_beq _ 1728 (by quickRfl)

end ECCompute
