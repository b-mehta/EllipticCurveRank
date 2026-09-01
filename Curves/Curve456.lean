/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 456 has rank at least 20

The elliptic curve recorded as
[curve 456](https://elliptic-rank.icarm.cloud/curve/456) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1205908701884023972043061821726860`   and
  `a₆ = 14443705704500032075948025770184419656032855664272`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 456 over `ℚ`. -/
@[expose] public def curve456 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1205908701884023972043061821726860, 14443705704500032075948025770184419656032855664272⟩

/-- ICARM leaderboard curve 456 has Mordell-Weil rank at least `20`. -/
public theorem curve456_hasRankGE_20 : HasRankGE curve456 20 := by
  unfold curve456
  certify_curve torsion 37 "data/curve456.txt" "data/curve456-labels.txt"

/-- Curve 456 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve456.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 456. -/
public theorem curve456_j : curve456.j = 193939824957975903905156896515068688876405556045690999219013686267963474003864531950972669519851500175041 / 22109580904243323101474980159758459092807147453162165592143262171871673898004061991715263307929600000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
