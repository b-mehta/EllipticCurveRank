/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 29 has rank at least 8

The elliptic curve recorded as
[curve 29](https://elliptic-rank.icarm.cloud/curve/29) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -6494556985832`   and
  `a₆ = 6351402068900282539`

over `ℚ`. It has Mordell-Weil rank at least `8`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 29 over `ℚ`. -/
@[expose] public def curve29 : WeierstrassCurve ℚ := ⟨1, -1, 1, -6494556985832, 6351402068900282539⟩

/-- ICARM leaderboard curve 29 has Mordell-Weil rank at least `8`. -/
public theorem curve29_hasRankGE_8 : HasRankGE curve29 8 := by
  unfold curve29
  certify_curve torsion 13 "data/curve29.txt" "data/curve29-labels.txt"

/-- Curve 29 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve29.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 29. -/
public theorem curve29_j : curve29.j = 41557056551105053406226740571712308087609 / 143866916815668933650169841696000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
