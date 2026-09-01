/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 438 has rank at least 20

The elliptic curve recorded as
[curve 438](https://elliptic-rank.icarm.cloud/curve/438) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -26643979890902407817591906993402300`   and
  `a₆ = 1665937119886856944539473116224248568755065751453424`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 438 over `ℚ`. -/
@[expose] public def curve438 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -26643979890902407817591906993402300,
    1665937119886856944539473116224248568755065751453424⟩

/-- ICARM leaderboard curve 438 has Mordell-Weil rank at least `20`. -/
public theorem curve438_hasRankGE_20 : HasRankGE curve438 20 := by
  unfold curve438
  certify_curve torsion 17 "data/curve438.txt" "data/curve438-labels.txt"

/-- Curve 438 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve438.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 438. -/
public theorem curve438_j : curve438.j = 69453286046550722967711001540266340410018657691835938471386220775515081578100950443680636521470866384 / 384654526264443451574534061576460767336337125309648489484858586965466827613879923233034073776653 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
