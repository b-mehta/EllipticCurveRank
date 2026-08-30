/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 20 has rank at least 6

The elliptic curve recorded as
[curve 20](https://elliptic-rank.icarm.cloud/curve/20) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -122985156`   and
  `a₆ = 232744673700`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 20 over `ℚ`. -/
@[expose] public def curve20 : WeierstrassCurve ℚ := ⟨0, -1, 0, -122985156, 232744673700⟩

/-- ICARM leaderboard curve 20 has Mordell-Weil rank at least `6`. -/
public theorem curve20_hasRankGE_6 : HasRankGE curve20 6 := by
  unfold curve20
  certify_curve oneTorsion 7812 31 "data/curve20.txt" "data/curve20-labels.txt"

/-- Curve 20 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve20.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 20. -/
public theorem curve20_j : curve20.j = 803603536618091542566827344 / 373668526980316722179025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
