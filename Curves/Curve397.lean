/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 397 has rank at least 22

The elliptic curve recorded as
[curve 397](https://elliptic-rank.icarm.cloud/curve/397) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -414358277117226597089349992018378`   and
  `a₆ = 4081054901154391944908039080891277227782032172248`

over `ℚ`. It has Mordell-Weil rank at least `22`.

Submitted to the leaderboard by Rayan Hatout.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 397 over `ℚ`. -/
@[expose] public def curve397 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -414358277117226597089349992018378, 4081054901154391944908039080891277227782032172248⟩

/-- ICARM leaderboard curve 397 has Mordell-Weil rank at least `22`. -/
public theorem curve397_hasRankGE_22 : HasRankGE curve397 22 := by
  unfold curve397
  certify_curve torsion 17 "data/curve397.txt" "data/curve397-labels.txt"

/-- Curve 397 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve397.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 397. -/
public theorem curve397_j : curve397.j = -7867772035879162626763025006949318607503813367726011469109045935072672855549794819954521149438721857561 / 2641855116834374132577871224152810511120637442035180975087019855118289801626482364997169495375887500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
