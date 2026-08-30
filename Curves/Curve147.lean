/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 147 has rank at least 18

The elliptic curve recorded as
[curve 147](https://elliptic-rank.icarm.cloud/curve/147) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -304375792648473160657575`   and
  `a₆ = 65348316359688219048467264095557961`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 147 over `ℚ`. -/
@[expose] public def curve147 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -304375792648473160657575, 65348316359688219048467264095557961⟩

/-- ICARM leaderboard curve 147 has Mordell-Weil rank at least `18`. -/
public theorem curve147_hasRankGE_18 : HasRankGE curve147 18 := by
  unfold curve147
  certify_curve torsion 17 "data/curve147.txt" "data/curve147-labels.txt"

/-- Curve 147 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve147.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 147. -/
public theorem curve147_j : curve147.j = -3118559544780734398050017625914583868005128181022561460140274470385125570801 / 40091900068111500354981590451888913785493616412246049722990279496695808 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
