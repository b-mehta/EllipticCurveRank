/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 382 has rank at least 18

The elliptic curve recorded as
[curve 382](https://elliptic-rank.icarm.cloud/curve/382) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -34917942850413226144077798077`   and
  `a₆ = 2481898466598513504719028897670995969469829`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by y011d4.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 382 over `ℚ`. -/
@[expose] public def curve382 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -34917942850413226144077798077, 2481898466598513504719028897670995969469829⟩

/-- ICARM leaderboard curve 382 has Mordell-Weil rank at least `18`. -/
public theorem curve382_hasRankGE_18 : HasRankGE curve382 18 := by
  unfold curve382
  certify_curve torsion 43 "data/curve382.txt" "data/curve382-labels.txt"

/-- Curve 382 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve382.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 382. -/
public theorem curve382_j : curve382.j = 6458655695030924799680837238449902603221686759966097418737315873593696049304830776225929 / 87384268844224104438296085063546882152108836445459219835470052461304735788797440000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
