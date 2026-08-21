/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.CompleteSquare
import ECCompute.Tactic.QuickRfl
import ECCompute.Kernel.Fold

/-!
# Certifying the j-invariant

The j-invariant `j = c₄³ / Δ` is an isomorphism invariant: it is the same for every Weierstrass
model of a curve (mathlib's `WeierstrassCurve.variableChange_j`), so it can be read off any integral
model `⟨a₁, …, a₆⟩`.

`j_eq_iff` reduces a claim `j = q` to the polynomial identity `c₄³ = Δ · q`, which each curve
discharges by `decide +kernel`; `isElliptic_of_Δ_ne_zero` supplies the `IsElliptic` instance from
a nonzero discriminant.
-/

namespace ECCompute

open WeierstrassCurve

/-- For a Weierstrass curve with invertible discriminant, `j = q` iff `c₄³ = Δ · q`. -/
theorem j_eq_iff {W : WeierstrassCurve ℚ} [W.IsElliptic] {q : ℚ} :
    W.j = q ↔ W.c₄ ^ 3 = W.Δ * q := by
  rw [WeierstrassCurve.j, Units.inv_mul_eq_iff_eq_mul, coe_Δ']

/-- Over `ℚ`, a nonzero discriminant makes a model an elliptic curve (so `j` is defined). -/
theorem isElliptic_of_Δ_ne_zero {W : WeierstrassCurve ℚ} (hΔ : W.Δ ≠ 0) : W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr hΔ⟩

end ECCompute
