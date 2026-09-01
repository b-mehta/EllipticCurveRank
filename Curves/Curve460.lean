/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 460 has rank at least 10

The elliptic curve recorded as
[curve 460](https://elliptic-rank.icarm.cloud/curve/460) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1255871985167`   and
  `a₆ = 532887973539695191`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 460 over `ℚ`. -/
@[expose] public def curve460 : WeierstrassCurve ℚ := ⟨1, -1, 1, -1255871985167, 532887973539695191⟩

/-- ICARM leaderboard curve 460 has Mordell-Weil rank at least `10`. -/
public theorem curve460_hasRankGE_10 : HasRankGE curve460 10 := by
  unfold curve460
  certify_curve torsion 13 "data/curve460.txt" "data/curve460-labels.txt"

/-- Curve 460 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve460.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 460. -/
public theorem curve460_j : curve460.j = 300491576315884259676139996638417555369 / 5617509494623919702732952064000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
