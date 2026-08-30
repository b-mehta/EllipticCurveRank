/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 166 has rank at least 17

The elliptic curve recorded as
[curve 166](https://elliptic-rank.icarm.cloud/curve/166) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3687257198396459595596432`   and
  `a₆ = 2724740878574131022947561407482810739`

over `ℚ`. It has Mordell-Weil rank at least `17`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 166 over `ℚ`. -/
@[expose] public def curve166 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -3687257198396459595596432, 2724740878574131022947561407482810739⟩

/-- ICARM leaderboard curve 166 has Mordell-Weil rank at least `17`. -/
public theorem curve166_hasRankGE_17 : HasRankGE curve166 17 := by
  unfold curve166
  certify_curve torsion 19 "data/curve166.txt" "data/curve166-labels.txt"

/-- Curve 166 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve166.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 166. -/
public theorem curve166_j : curve166.j = 7605127164328521086410893863528841271018548599265400258335350798998117793209 / 1581713212839919538549215829096503759085229478779799109779343216640000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
