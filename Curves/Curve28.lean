/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 28 has rank at least 7

The elliptic curve recorded as
[curve 28](https://elliptic-rank.icarm.cloud/curve/28) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3289744045996`   and
  `a₆ = 2272951313488252420`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 28 over `ℚ`. -/
@[expose] public def curve28 : WeierstrassCurve ℚ := ⟨0, -1, 0, -3289744045996, 2272951313488252420⟩

/-- ICARM leaderboard curve 28 has Mordell-Weil rank at least `7`. -/
public theorem curve28_hasRankGE_7 : HasRankGE curve28 7 := by
  unfold curve28
  certify_curve oneTorsion 3836452 43 "data/curve28.txt" "data/curve28-labels.txt"

/-- Curve 28 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve28.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 28. -/
public theorem curve28_j : curve28.j = 15380486595963878931284986830701025482704 / 182608770943041829223331085857933525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
