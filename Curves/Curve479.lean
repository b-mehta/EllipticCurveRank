/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 479 has rank at least 9

The elliptic curve recorded as
[curve 479](https://elliptic-rank.icarm.cloud/curve/479) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -197123177`   and
  `a₆ = 1056496302505`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 479 over `ℚ`. -/
@[expose] public def curve479 : WeierstrassCurve ℚ := ⟨1, -1, 1, -197123177, 1056496302505⟩

/-- ICARM leaderboard curve 479 has Mordell-Weil rank at least `9`. -/
public theorem curve479_hasRankGE_9 : HasRankGE curve479 9 := by
  unfold curve479
  certify_curve torsion 7 "data/curve479.txt" "data/curve479-labels.txt"

/-- Curve 479 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve479.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 479. -/
public theorem curve479_j : curve479.j = 1162008357699856965485555529 / 11077616079423039213568 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
