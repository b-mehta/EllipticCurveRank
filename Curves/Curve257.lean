/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 257 has rank at least 7

The elliptic curve recorded as
[curve 257](https://elliptic-rank.icarm.cloud/curve/257) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 159359`   and
  `a₆ = 101761`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 257 over `ℚ`. -/
@[expose] public def curve257 : WeierstrassCurve ℚ := ⟨0, 0, 0, 159359, 101761⟩

/-- ICARM leaderboard curve 257 has Mordell-Weil rank at least `7`. -/
public theorem curve257_hasRankGE_7 : HasRankGE curve257 7 := by
  unfold curve257
  certify_curve torsion 79 "data/curve257.txt" "data/curve257-labels.txt"

/-- Curve 257 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve257.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 257. -/
public theorem curve257_j : curve257.j = 27972643918500488448 / 16188152231151383 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
