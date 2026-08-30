/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 346 has rank at least 19

The elliptic curve recorded as
[curve 346](https://elliptic-rank.icarm.cloud/curve/346) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1650879174392173933380282511725`   and
  `a₆ = 827912259081400825673880665852533513855100625`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by Christopher R.
Hill.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 346 over `ℚ`. -/
@[expose] public def curve346 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1650879174392173933380282511725, 827912259081400825673880665852533513855100625⟩

/-- ICARM leaderboard curve 346 has Mordell-Weil rank at least `19`. -/
public theorem curve346_hasRankGE_19 : HasRankGE curve346 19 := by
  unfold curve346
  certify_curve torsion 7 "data/curve346.txt" "data/curve346-labels.txt"

/-- Curve 346 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve346.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 346. -/
public theorem curve346_j : curve346.j = -497587634412316695468599019472446112983691560731908827698521707090365944734792679503752065208401 / 8153715222927956302195203530071282231036456187252543215356220806381515287867179840000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
