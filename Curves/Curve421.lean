/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 421 has rank at least 20

The elliptic curve recorded as
[curve 421](https://elliptic-rank.icarm.cloud/curve/421) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -9174555732805735926833867064540`   and
  `a₆ = 10766496995514664777353668694668185576606491888`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 421 over `ℚ`. -/
@[expose] public def curve421 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -9174555732805735926833867064540, 10766496995514664777353668694668185576606491888⟩

/-- ICARM leaderboard curve 421 has Mordell-Weil rank at least `20`. -/
public theorem curve421_hasRankGE_20 : HasRankGE curve421 20 := by
  unfold curve421
  certify_curve torsion 23 "data/curve421.txt" "data/curve421-labels.txt"

/-- Curve 421 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve421.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 421. -/
public theorem curve421_j : curve421.j = -138946213617053377829338182089916505498172730542175716646113249857591609931200854512800570576 / 1061827858705220506007842685101938445261211871778999746452629148646075956317806286921875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
