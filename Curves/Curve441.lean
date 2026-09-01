/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 441 has rank at least 23

The elliptic curve recorded as
[curve 441](https://elliptic-rank.icarm.cloud/curve/441) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1009193317631438952446667509552594424471980395090`   and
  `a₆ = 393673064651019213659149270108184935843722977273821305373879015181970692`

over `ℚ`. It has Mordell-Weil rank at least `23`. Submitted to the leaderboard by Nikita-Shulga.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 441 over `ℚ`. -/
@[expose] public def curve441 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1009193317631438952446667509552594424471980395090,
    393673064651019213659149270108184935843722977273821305373879015181970692⟩

/-- ICARM leaderboard curve 441 has Mordell-Weil rank at least `23`. -/
public theorem curve441_hasRankGE_23 : HasRankGE curve441 23 := by
  unfold curve441
  certify_curve torsion 31 "data/curve441.txt" "data/curve441-labels.txt"

/-- Curve 441 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve441.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 441. -/
public theorem curve441_j : curve441.j = -60651272127304382073348219761142510335173676753610415745150974122445073897492820517292748812405546821936591392953337518079706425573208958334001 / 623911263467091140233152014458308742867238745769821140750614942189532820475733007539958665099993085300666717140827187673615080988672000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
