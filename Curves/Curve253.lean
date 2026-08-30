/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 253 has rank at least 7

The elliptic curve recorded as
[curve 253](https://elliptic-rank.icarm.cloud/curve/253) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 43319`   and
  `a₆ = 61009`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 253 over `ℚ`. -/
@[expose] public def curve253 : WeierstrassCurve ℚ := ⟨0, 0, 0, 43319, 61009⟩

/-- ICARM leaderboard curve 253 has Mordell-Weil rank at least `7`. -/
public theorem curve253_hasRankGE_7 : HasRankGE curve253 7 := by
  unfold curve253
  certify_curve torsion 23 "data/curve253.txt" "data/curve253-labels.txt"

/-- Curve 253 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve253.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 253. -/
public theorem curve253_j : curve253.j = 561874078983806208 / 325259107171223 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
