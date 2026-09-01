/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 472 has rank at least 10

The elliptic curve recorded as
[curve 472](https://elliptic-rank.icarm.cloud/curve/472) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -8613625056`   and
  `a₆ = 344966450788353`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 472 over `ℚ`. -/
@[expose] public def curve472 : WeierstrassCurve ℚ := ⟨1, 1, 1, -8613625056, 344966450788353⟩

/-- ICARM leaderboard curve 472 has Mordell-Weil rank at least `10`. -/
public theorem curve472_hasRankGE_10 : HasRankGE curve472 10 := by
  unfold curve472
  certify_curve torsion 7 "data/curve472.txt" "data/curve472-labels.txt"

/-- Curve 472 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve472.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 472. -/
public theorem curve472_j : curve472.j = -70677568828307615974483580445408769 / 10508499001278316988602577510400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
