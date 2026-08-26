/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

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

/-- ICARM leaderboard curve 14, `y² = x³ - x² - 24649 x + 1355209` over `ℚ`. -/
@[expose] public def curve14 : WeierstrassCurve ℚ := ⟨0, -1, 0, -24649, 1355209⟩

/-- ICARM leaderboard curve 14 has Mordell-Weil rank at least `4`, with full rational
`2`-torsion. -/
public theorem curve14_hasRankGE_4 : HasRankGE curve14 4 := by
  unfold curve14
  certify_curve fullTorsion "data/curve14.txt" "data/curve14-labels.txt"

/-- Curve 14 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve14.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 14. -/
public theorem curve14_j : curve14.j = 404370344147392 / 42649271289 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
