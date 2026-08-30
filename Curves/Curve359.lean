/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 359 has rank at least 10

The elliptic curve recorded as
[curve 359](https://elliptic-rank.icarm.cloud/curve/359) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -306746316`   and
  `a₆ = 2202727337316`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 359 over `ℚ`. -/
@[expose] public def curve359 : WeierstrassCurve ℚ := ⟨0, -1, 0, -306746316, 2202727337316⟩

/-- ICARM leaderboard curve 359 has Mordell-Weil rank at least `10`. -/
public theorem curve359_hasRankGE_10 : HasRankGE curve359 10 := by
  unfold curve359
  certify_curve torsion 17 "data/curve359.txt" "data/curve359-labels.txt"

/-- Curve 359 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve359.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 359. -/
public theorem curve359_j : curve359.j = -12468718350418033281788549584 / 971309421327543832019475 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
