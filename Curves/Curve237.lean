/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 237 has rank at least 15

The elliptic curve recorded as
[curve 237](https://elliptic-rank.icarm.cloud/curve/237) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1651640332674597876`   and
  `a₆ = 910715925208661721534017824`

over `ℚ`. It has Mordell-Weil rank at least `15`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 237 over `ℚ`. -/
@[expose] public def curve237 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -1651640332674597876, 910715925208661721534017824⟩

/-- ICARM leaderboard curve 237 has Mordell-Weil rank at least `15`. -/
public theorem curve237_hasRankGE_15 : HasRankGE curve237 15 := by
  unfold curve237
  certify_curve torsion 7 "data/curve237.txt" "data/curve237-labels.txt"

/-- Curve 237 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve237.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 237. -/
public theorem curve237_j : curve237.j = -1946391439876672140173052168690310817866922804412332755024 / 273234466801760635227068420743544928740525146081582975 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
