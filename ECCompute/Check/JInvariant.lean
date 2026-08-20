/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.ModelIso
import ECCompute.QuickRfl
import ECCompute.Check.Fold

/-!
# Certifying the j-invariant

The j-invariant `j = c₄³ / Δ` is an isomorphism invariant: it is the same for every Weierstrass
model of a curve (mathlib's `WeierstrassCurve.variableChange_j`), so it can be read off any integral
model `⟨a₁, …, a₆⟩`.

`j_eq_iff` reduces a claim `j = q` to the polynomial identity `c₄³ = Δ · q`; the per-curve
obligation is then the kernel-reducible `Bool` check `(c₄³ == Δ · q) = true`, discharged by
`j_eq_of_beq`.
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

/-- Kernel-reducible `ℚ` equality: `Int.beq'` on numerators and `Nat.beq` on denominators. -/
noncomputable def ratBeq' (a b : ℚ) : Bool := (Int.beq' a.num b.num).and' (Nat.beq a.den b.den)

/-- `ratBeq'` agrees with `==` on `ℚ`. -/
theorem ratBeq'_eq (a b : ℚ) : ratBeq' a b = (a == b) := by
  rw [ratBeq', Bool.and'_eq_and, Int.beq'_eq_beq, ← natBeqEq]
  rcases eq_or_ne a b with h | h
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, Bool.and_eq_false_iff]
    by_contra hc
    rw [not_or, Bool.not_eq_false, Bool.not_eq_false, beq_iff_eq, beq_iff_eq] at hc
    exact h (Rat.ext hc.1 hc.2)

/-- `IsElliptic` from a kernel-reducible `Bool` witness that `Δ ≠ 0`. -/
theorem isElliptic_of_bne {W : WeierstrassCurve ℚ} (h : (ratBeq' W.Δ 0).not' = true) :
    W.IsElliptic :=
  isElliptic_of_Δ_ne_zero (by simpa [Bool.not'_eq_not, ratBeq'_eq] using h)

/-- `j = q` from a kernel-reducible `Bool` witness that `c₄³ = Δ · q`. -/
theorem j_eq_of_beq (W : WeierstrassCurve ℚ) [W.IsElliptic] (q : ℚ)
    (h : ratBeq' (W.c₄ ^ 3) (W.Δ * q) = true) : W.j = q :=
  (j_eq_iff W q).mpr (eq_of_beq (by rwa [ratBeq'_eq] at h))

end ECCompute
