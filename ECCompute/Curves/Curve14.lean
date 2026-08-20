/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify
import ECCompute.Check.JInvariant

/-!
# Curve 14 has rank at least 4, with full rational 2-torsion

The elliptic curve recorded as
[curve 14](https://elliptic-rank.icarm.cloud/curve/14) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² - 24649 x + 1355209`

over `ℚ`, of Mordell-Weil rank at least `4` (a curve of Wiman, 1945). Its `2`-division cubic
factors completely, `x³ - x² - 24649 x + 1355209 = (x - 67)(x - 113)(x + 179)`, so `E` has full
rational `2`-torsion `E(ℚ)[2] ≅ (ℤ/2)²`, i.e. `t = 2`, and its discriminant is a perfect square.

The certificate gives `ρ = 6` points with `𝔽₂`-independent descent images (the four rational
points of infinite order plus the two `2`-torsion points `(67, 0)`, `(113, 0)`) and bounds the
two torsion dimensions by `|E(ℚ)[2]| ≤ 4 = 2²`, giving `rank ≥ ρ - t = 6 - 2 = 4`. Points
(short-model coordinates) in `data/curve14.txt`, descent labels in `data/curve14-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₂` coefficient of ICARM leaderboard curve 14. -/
abbrev curve14A₂ : ℚ := -1

/-- The `a₄` coefficient of ICARM leaderboard curve 14. -/
abbrev curve14A₄ : ℚ := -24649

/-- The `a₆` coefficient of ICARM leaderboard curve 14. -/
abbrev curve14A₆ : ℚ := 1355209

/-- ICARM leaderboard curve 14, `y² = x³ - x² - 24649 x + 1355209` over `ℚ`. -/
def curve14 : WeierstrassCurve ℚ := ⟨0, curve14A₂, 0, curve14A₄, curve14A₆⟩

/-- ICARM leaderboard curve 14 has Mordell-Weil rank at least `4`, despite full rational
`2`-torsion. -/
theorem curve14_hasRankGE_4 : HasRankGE curve14 4 := by
  unfold curve14 curve14A₂ curve14A₄ curve14A₆
  certify_curve fullTorsion points "data/curve14.txt" labels "data/curve14-labels.txt"

/-- Curve 14 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve14.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of curve 14. -/
theorem curve14_j : curve14.j = 404370344147392 / 42649271289 :=
  j_eq_of_beq _ _ (by quickRfl)

end ECCompute
