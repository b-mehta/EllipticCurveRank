/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 392 has rank at least 9

The elliptic curve recorded as
[curve 392](https://elliptic-rank.icarm.cloud/curve/392) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -936464551`   and
  `a₆ = 11031352038749`

over `ℚ`. It has Mordell-Weil rank at least `9`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 392 over `ℚ`. -/
@[expose] public def curve392 : WeierstrassCurve ℚ := ⟨1, 1, 1, -936464551, 11031352038749⟩

/-- ICARM leaderboard curve 392 has Mordell-Weil rank at least `9`. -/
public theorem curve392_hasRankGE_9 : HasRankGE curve392 9 := by
  unfold curve392
  certify_curve torsion 11 "data/curve392.txt" "data/curve392-labels.txt"

/-- Curve 392 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve392.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 392. -/
public theorem curve392_j : curve392.j = -90823396437863227068686159812849 / 14277544295858814611865600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
