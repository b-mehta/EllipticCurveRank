/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 197 has rank at least 14

The elliptic curve recorded as
[curve 197](https://elliptic-rank.icarm.cloud/curve/197) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -15848001975027331832`   and
  `a₆ = 24771530688804644612096284539`

over `ℚ`. It has Mordell-Weil rank at least `14`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 197 over `ℚ`. -/
@[expose] public def curve197 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -15848001975027331832, 24771530688804644612096284539⟩

/-- ICARM leaderboard curve 197 has Mordell-Weil rank at least `14`. -/
public theorem curve197_hasRankGE_14 : HasRankGE curve197 14 := by
  unfold curve197
  certify_curve torsion 23 "data/curve197.txt" "data/curve197-labels.txt"

/-- Curve 197 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve197.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 197. -/
public theorem curve197_j : curve197.j = -603837018010429905962106680915507932995274742781155586583609 / 14189122707727539011476117024355203566457751304284160000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
