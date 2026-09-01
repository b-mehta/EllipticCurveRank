/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 423 has rank at least 28

The elliptic curve recorded as
[curve 423](https://elliptic-rank.icarm.cloud/curve/423) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -277762374045498166503978906288594827838146361987727860020`   and
  `a₆ = 1745716564920954436762537886066484987032789883722113978504519639885660024203`
  `     054176400`

over `ℚ`. It has Mordell-Weil rank at least `28`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 423 over `ℚ`. -/
@[expose] public def curve423 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -277762374045498166503978906288594827838146361987727860020,
    1745716564920954436762537886066484987032789883722113978504519639885660024203054176400⟩

/-- ICARM leaderboard curve 423 has Mordell-Weil rank at least `28`. -/
public theorem curve423_hasRankGE_28 : HasRankGE curve423 28 := by
  unfold curve423
  certify_curve torsion 23 "data/curve423.txt" "data/curve423-labels.txt"

/-- Curve 423 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve423.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 423. -/
public theorem curve423_j : curve423.j = 2369976056690869180800014580594574845307674307358508590680361204117326490300654023841439423903394559456586162960419536535844443166400635716827951592412181355393425411376143681 / 54982549279076737648560456645555796539139519502785293433793118087871249992058975961811051872139310047478232925568429450545689426273411586773356193898145626236206080000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
