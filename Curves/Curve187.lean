/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 187 has rank at least 17

The elliptic curve recorded as
[curve 187](https://elliptic-rank.icarm.cloud/curve/187) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1189299700325816602093307071`   and
  `a₆ = 15790705709481148712666898533494358863001`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 187 over `ℚ`. -/
@[expose] public def curve187 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1189299700325816602093307071, 15790705709481148712666898533494358863001⟩

/-- ICARM leaderboard curve 187 has Mordell-Weil rank at least `17`. -/
public theorem curve187_hasRankGE_17 : HasRankGE curve187 17 := by
  unfold curve187
  certify_curve torsion 37 "data/curve187.txt" "data/curve187-labels.txt"

/-- Curve 187 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve187.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 187. -/
public theorem curve187_j : curve187.j = -6513647187543870833172410756270145944047250180835110110077755581497080214919973089 / 2022211713991403952643989329426518524793000170608832607992621018508718899200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
