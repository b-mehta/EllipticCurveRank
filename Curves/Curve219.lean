/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 219 has rank at least 17

The elliptic curve recorded as
[curve 219](https://elliptic-rank.icarm.cloud/curve/219) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -76542275904763760832149`   and
  `a₆ = 4899787800875052237542378473282316`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 219 over `ℚ`. -/
@[expose] public def curve219 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -76542275904763760832149, 4899787800875052237542378473282316⟩

/-- ICARM leaderboard curve 219 has Mordell-Weil rank at least `17`. -/
public theorem curve219_hasRankGE_17 : HasRankGE curve219 17 := by
  unfold curve219
  certify_curve torsion 17 "data/curve219.txt" "data/curve219-labels.txt"

/-- Curve 219 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve219.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 219. -/
public theorem curve219_j : curve219.j = 49593850241039536270516133526307573019601834553795431231177253841479535689 / 18328723162152475758783373844977983009407970299659748341711623258000900 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
