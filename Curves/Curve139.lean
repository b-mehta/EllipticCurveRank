/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 139 has rank at least 11

The elliptic curve recorded as
[curve 139](https://elliptic-rank.icarm.cloud/curve/139) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -56880994`   and
  `a₆ = 168642718624`

over `ℚ`. It has Mordell-Weil rank at least `11`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 139 over `ℚ`. -/
@[expose] public def curve139 : WeierstrassCurve ℚ := ⟨1, -1, 0, -56880994, 168642718624⟩

/-- ICARM leaderboard curve 139 has Mordell-Weil rank at least `11`. -/
public theorem curve139_hasRankGE_11 : HasRankGE curve139 11 := by
  unfold curve139
  certify_curve torsion 7 "data/curve139.txt" "data/curve139-labels.txt"

/-- Curve 139 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve139.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 139. -/
public theorem curve139_j : curve139.j = -20352850745542350272894906361 / 505896333231836385777788 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
