/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 89 has rank at least 13

The elliptic curve recorded as
[curve 89](https://elliptic-rank.icarm.cloud/curve/89) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -6529826212`   and
  `a₆ = 195995662948900`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 89 over `ℚ`. -/
@[expose] public def curve89 : WeierstrassCurve ℚ := ⟨0, 0, 0, -6529826212, 195995662948900⟩

/-- ICARM leaderboard curve 89 has Mordell-Weil rank at least `13`. -/
public theorem curve89_hasRankGE_13 : HasRankGE curve89 13 := by
  unfold curve89
  certify_curve torsion 7 "data/curve89.txt" "data/curve89-labels.txt"

/-- Curve 89 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve89.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 89. -/
public theorem curve89_j : curve89.j = 120278669541754867122691336375296 / 4781580467928154293492273157 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
