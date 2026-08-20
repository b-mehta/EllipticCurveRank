/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Check.JInvariant

/-!
# Wiman's curve has rank at least 4

The elliptic curve

  `E : y² = x³ - x² - 24649 x + 1355209`

over `ℚ` has Mordell-Weil rank at least `4` (a curve of Wiman, 1945). Its `2`-division cubic
factors completely, `x³ - x² - 24649 x + 1355209 = (x - 67)(x - 113)(x + 179)`, so `E` has full
rational `2`-torsion `E(ℚ)[2] ≅ (ℤ/2)²`, i.e. `t = 2`, and its discriminant is a perfect square.

The certificate gives `ρ = 6` points with `𝔽₂`-independent descent images (the four rational
points of infinite order plus the two `2`-torsion points `(67, 0)`, `(113, 0)`) and bounds the
two torsion dimensions by `|E(ℚ)[2]| ≤ 4 = 2²`, giving `rank ≥ ρ - t = 6 - 2 = 4`. Points
(short-model coordinates) in `data/wiman4.txt`, descent labels in `data/wiman4-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- Wiman's curve `y² = x³ - x² - 24649 x + 1355209` over `ℚ`. Certified rank ≥ 4 in
`curveWiman4_hasRankGE_4`. -/
def curveWiman4 : WeierstrassCurve ℚ := ⟨0, -1, 0, -24649, 1355209⟩

/-- Wiman's curve has Mordell-Weil rank at least `4`, with full rational `2`-torsion. -/
theorem curveWiman4_hasRankGE_4 : HasRankGE curveWiman4 4 := by
  unfold curveWiman4
  certify_curve fullTorsion points "data/wiman4.txt" labels "data/wiman4-labels.txt"

/-- Wiman's curve is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curveWiman4.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of Wiman's curve. -/
theorem curveWiman4_j : curveWiman4.j = 404370344147392 / 42649271289 :=
  j_eq_of_beq _ _ (by quickRfl)

end ECCompute
