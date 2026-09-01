/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 480 has rank at least 8

The elliptic curve recorded as
[curve 480](https://elliptic-rank.icarm.cloud/curve/480) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -257481715`   and
  `a₆ = 1584902692961`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 480 over `ℚ`. -/
@[expose] public def curve480 : WeierstrassCurve ℚ := ⟨1, 0, 0, -257481715, 1584902692961⟩

/-- ICARM leaderboard curve 480 has Mordell-Weil rank at least `8`. -/
public theorem curve480_hasRankGE_8 : HasRankGE curve480 8 := by
  unfold curve480
  certify_curve torsion 13 "data/curve480.txt" "data/curve480-labels.txt"

/-- Curve 480 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve480.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 480. -/
public theorem curve480_j : curve480.j = 1887830036553530140618195082161 / 7316903969389859153190912 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
