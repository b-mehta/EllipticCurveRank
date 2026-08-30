/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 265 has rank at least 7

The elliptic curve recorded as
[curve 265](https://elliptic-rank.icarm.cloud/curve/265) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 54722`   and
  `a₆ = 519841`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 265 over `ℚ`. -/
@[expose] public def curve265 : WeierstrassCurve ℚ := ⟨0, 0, 0, 54722, 519841⟩

/-- ICARM leaderboard curve 265 has Mordell-Weil rank at least `7`. -/
public theorem curve265_hasRankGE_7 : HasRankGE curve265 7 := by
  unfold curve265
  certify_curve torsion 5 "data/curve265.txt" "data/curve265-labels.txt"

/-- Curve 265 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve265.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 265. -/
public theorem curve265_j : curve265.j = 1132634053152331776 / 662755857462779 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
