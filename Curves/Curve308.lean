/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 308 has rank at least 15

The elliptic curve recorded as
[curve 308](https://elliptic-rank.icarm.cloud/curve/308) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 24537619889008718205152851658505801`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 308 over `ℚ`. -/
@[expose] public def curve308 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 0, 24537619889008718205152851658505801⟩

/-- ICARM leaderboard curve 308 has Mordell-Weil rank at least `15`. -/
public theorem curve308_hasRankGE_15 : HasRankGE curve308 15 := by
  unfold curve308
  certify_curve torsion 7 "data/curve308.txt" "data/curve308-labels.txt"

/-- Curve 308 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve308.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 308. -/
public theorem curve308_j : curve308.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
