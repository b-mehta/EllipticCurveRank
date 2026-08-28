/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 192 has rank at least 15

The elliptic curve recorded as
[curve 192](https://elliptic-rank.icarm.cloud/curve/192) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -851556499645504323141`   and
  `a₆ = 9487026023034811912831219901121`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve192.txt`; descent labels are in
`data/curve192-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 192 over `ℚ`. -/
@[expose] public def curve192 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -851556499645504323141, 9487026023034811912831219901121⟩

/-- ICARM leaderboard curve 192 has Mordell-Weil rank at least `15`. -/
public theorem curve192_hasRankGE_15 : HasRankGE curve192 15 := by
  unfold curve192
  certify_curve torsion 29 "data/curve192.txt" "data/curve192-labels.txt"

/-- Curve 192 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve192.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 192. -/
public theorem curve192_j : curve192.j = 68291101305258982483432261487858729291933753921200475425843118086609 / 638730941704979414939006251941574649893567559880993486621081600 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
