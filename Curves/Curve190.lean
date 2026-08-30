/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 190 has rank at least 17

The elliptic curve recorded as
[curve 190](https://elliptic-rank.icarm.cloud/curve/190) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -462840480498050459959650246`   and
  `a₆ = 3815301189936260852812257361005424248676`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 190 over `ℚ`. -/
@[expose] public def curve190 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -462840480498050459959650246, 3815301189936260852812257361005424248676⟩

/-- ICARM leaderboard curve 190 has Mordell-Weil rank at least `17`. -/
public theorem curve190_hasRankGE_17 : HasRankGE curve190 17 := by
  unfold curve190
  certify_curve torsion 37 "data/curve190.txt" "data/curve190-labels.txt"

/-- Curve 190 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve190.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 190. -/
public theorem curve190_j : curve190.j = 383923158845566564666580665798600967317629666608480381388681118782283799897454289 / 2002759759339260333083343920570400172836681708972713617207563581365767372800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
