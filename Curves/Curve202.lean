/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 202 has rank at least 13

The elliptic curve recorded as
[curve 202](https://elliptic-rank.icarm.cloud/curve/202) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -7699301552946471111`   and
  `a₆ = 8260370960120371675267448841`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 202 over `ℚ`. -/
@[expose] public def curve202 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -7699301552946471111, 8260370960120371675267448841⟩

/-- ICARM leaderboard curve 202 has Mordell-Weil rank at least `13`. -/
public theorem curve202_hasRankGE_13 : HasRankGE curve202 13 := by
  unfold curve202
  certify_curve torsion 17 "data/curve202.txt" "data/curve202-labels.txt"

/-- Curve 202 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve202.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 202. -/
public theorem curve202_j : curve202.j = -50475159630885686836045435118623556053061319140412913983810289 / 266808849431496166419387240071765982358706830625053900800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
