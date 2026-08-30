/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 263 has rank at least 8

The elliptic curve recorded as
[curve 263](https://elliptic-rank.icarm.cloud/curve/263) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -6243121`   and
  `a₆ = 181090849`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 263 over `ℚ`. -/
@[expose] public def curve263 : WeierstrassCurve ℚ := ⟨0, 0, 0, -6243121, 181090849⟩

/-- ICARM leaderboard curve 263 has Mordell-Weil rank at least `8`. -/
public theorem curve263_hasRankGE_8 : HasRankGE curve263 8 := by
  unfold curve263
  certify_curve torsion 11 "data/curve263.txt" "data/curve263-labels.txt"

/-- Curve 263 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve263.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 263. -/
public theorem curve263_j : curve263.j = 1681934140505088418597632 / 972456081315028640617 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
