/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 406 has rank at least 18

The elliptic curve recorded as
[curve 406](https://elliptic-rank.icarm.cloud/curve/406) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -21097251078837597697404902`   and
  `a₆ = 37018745916232850579640184758127094901`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 406 over `ℚ`. -/
@[expose] public def curve406 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -21097251078837597697404902, 37018745916232850579640184758127094901⟩

/-- ICARM leaderboard curve 406 has Mordell-Weil rank at least `18`. -/
public theorem curve406_hasRankGE_18 : HasRankGE curve406 18 := by
  unfold curve406
  certify_curve torsion 31 "data/curve406.txt" "data/curve406-labels.txt"

/-- Curve 406 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve406.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 406. -/
public theorem curve406_j : curve406.j = 1424537211143632906429068508511158109875595217523000559559570235044292388431129 / 12303449509474462298669957222976879904473937131578840667199591419187200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
