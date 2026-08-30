/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 65 has rank at least 25

The elliptic curve recorded as
[curve 65](https://elliptic-rank.icarm.cloud/curve/65) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1222583105876029916237789137035775062690200`   and
  `a₆ = 523967447200209449943328506898413682821590945806099349816040000`

over `ℚ`. It has Mordell-Weil rank at least `25`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 65 over `ℚ`. -/
@[expose] public def curve65 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1222583105876029916237789137035775062690200,
    523967447200209449943328506898413682821590945806099349816040000⟩

/-- ICARM leaderboard curve 65 has Mordell-Weil rank at least `25`. -/
public theorem curve65_hasRankGE_25 : HasRankGE curve65 25 := by
  unfold curve65
  certify_curve torsion 23 "data/curve65.txt" "data/curve65-labels.txt"

/-- Curve 65 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve65.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 65. -/
public theorem curve65_j : curve65.j = -202096542159422198898674776173816549955496049738612716727844469925310546840605901865863706389701428955168474644189762367560151868801 / 1648077180048519919196851388268507997232089165506048976474499224670899793965899322864689351309245989194390271909250018304000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
