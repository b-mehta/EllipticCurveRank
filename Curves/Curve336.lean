/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 336 has rank at least 19

The elliptic curve recorded as
[curve 336](https://elliptic-rank.icarm.cloud/curve/336) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -15562580896796750296231806771530`   and
  `a₆ = 23456109321321254485649290545253053437231113097`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 336 over `ℚ`. -/
@[expose] public def curve336 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -15562580896796750296231806771530, 23456109321321254485649290545253053437231113097⟩

/-- ICARM leaderboard curve 336 has Mordell-Weil rank at least `19`. -/
public theorem curve336_hasRankGE_19 : HasRankGE curve336 19 := by
  unfold curve336
  certify_curve torsion 23 "data/curve336.txt" "data/curve336-labels.txt"

/-- Curve 336 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve336.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 336. -/
public theorem curve336_j : curve336.j = 36594938676152071796442772108390849057492999144015417191588096250542274439806319324943995857 / 311196843453773881703125985818778750182512436148219571655715148923354100764098317778944 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
