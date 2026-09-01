/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 87 has rank at least 18

The elliptic curve recorded as
[curve 87](https://elliptic-rank.icarm.cloud/curve/87) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -128067973760200094197595276`   and
  `a₆ = 551283524310015496401062930694209419949`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 87 over `ℚ`. -/
@[expose] public def curve087 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -128067973760200094197595276, 551283524310015496401062930694209419949⟩

/-- ICARM leaderboard curve 87 has Mordell-Weil rank at least `18`. -/
public theorem curve087_hasRankGE_18 : HasRankGE curve087 18 := by
  unfold curve087
  certify_curve torsion 17 "data/curve087.txt" "data/curve087-labels.txt"

/-- Curve 87 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve087.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 87. -/
public theorem curve087_j : curve087.j = 232297923224273661598497112183422964494734283884179865519609450657998763481810157249 / 3141026088650294736579116234013850169228851134468835623113068971509123596492800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
