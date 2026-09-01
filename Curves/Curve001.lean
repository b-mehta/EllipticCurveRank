/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 1 has rank at least 12

The elliptic curve recorded as
[curve 1](https://elliptic-rank.icarm.cloud/curve/1) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -6349808647`   and
  `a₆ = 193146346911036`

over `ℚ`. It has Mordell-Weil rank at least `12`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 1 over `ℚ`. -/
@[expose] public def curve001 : WeierstrassCurve ℚ := ⟨0, 0, 1, -6349808647, 193146346911036⟩

/-- ICARM leaderboard curve 1 has Mordell-Weil rank at least `12`. -/
public theorem curve001_hasRankGE_12 : HasRankGE curve001 12 := by
  unfold curve001
  certify_curve torsion 7 "data/curve001.txt" "data/curve001-labels.txt"

/-- Curve 1 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve001.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 1. -/
public theorem curve001_j : curve001.j = 28314286741481442530066036787695616 / 269601712590130409544942497797 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
