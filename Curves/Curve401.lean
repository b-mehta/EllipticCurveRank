/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 401 has rank at least 27

The elliptic curve recorded as
[curve 401](https://elliptic-rank.icarm.cloud/curve/401) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -94624210289371976970836667748793555136557175`   and
  `a₆ = 356735513818524391040758052970937761657716127823131580058975168250`

over `ℚ`. It has Mordell-Weil rank at least `27`.

Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 401 over `ℚ`. -/
@[expose] public def curve401 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -94624210289371976970836667748793555136557175,
    356735513818524391040758052970937761657716127823131580058975168250⟩

/-- ICARM leaderboard curve 401 has Mordell-Weil rank at least `27`. -/
public theorem curve401_hasRankGE_27 : HasRankGE curve401 27 := by
  unfold curve401
  certify_curve torsion 19 "data/curve401.txt" "data/curve401-labels.txt"

/-- Curve 401 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve401.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 401. -/
public theorem curve401_j : curve401.j = -13382918600625857335997524990265996642932576167788690918683487936008853656027667774920757309082091251064765905279002807695824 / 107553205467814304019096825942534431000736889727717739538830973347619492173257407050628227295918410158121168306205318355 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
