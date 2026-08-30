/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 353 has rank at least 9

The elliptic curve recorded as
[curve 353](https://elliptic-rank.icarm.cloud/curve/353) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -50591622`   and
  `a₆ = 140974764984`

over `ℚ`. It has Mordell-Weil rank at least `9`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 353 over `ℚ`. -/
@[expose] public def curve353 : WeierstrassCurve ℚ := ⟨1, 1, 0, -50591622, 140974764984⟩

/-- ICARM leaderboard curve 353 has Mordell-Weil rank at least `9`. -/
public theorem curve353_hasRankGE_9 : HasRankGE curve353 9 := by
  unfold curve353
  certify_curve torsion 7 "data/curve353.txt" "data/curve353-labels.txt"

/-- Curve 353 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve353.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 353. -/
public theorem curve353_j : curve353.j = -14320544650303169791402548841 / 300733579435137404332500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
