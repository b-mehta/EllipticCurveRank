/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 409 has rank at least 18

The elliptic curve recorded as
[curve 409](https://elliptic-rank.icarm.cloud/curve/409) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -444676196280094399128563694`   and
  `a₆ = 3297768615148916483027180606633461900200`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 409 over `ℚ`. -/
@[expose] public def curve409 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -444676196280094399128563694, 3297768615148916483027180606633461900200⟩

/-- ICARM leaderboard curve 409 has Mordell-Weil rank at least `18`. -/
public theorem curve409_hasRankGE_18 : HasRankGE curve409 18 := by
  unfold curve409
  certify_curve torsion 43 "data/curve409.txt" "data/curve409-labels.txt"

/-- Curve 409 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve409.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 409. -/
public theorem curve409_j : curve409.j = 13339139981366625591177477248205984683914974386440731276593711619212815561530141409 / 1274800621625408053628233687868083940035407967891958529527740244423722556437500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
