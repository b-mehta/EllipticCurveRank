/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 32 has rank at least 10

The elliptic curve recorded as
[curve 32](https://elliptic-rank.icarm.cloud/curve/32) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3414948705808928485`   and
  `a₆ = 1462640470912335058581199361`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve32.txt`; descent labels are in
`data/curve32-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 32 over `ℚ`. -/
@[expose] public def curve32 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3414948705808928485, 1462640470912335058581199361⟩

/-- ICARM leaderboard curve 32 has Mordell-Weil rank at least `10`. -/
public theorem curve32_hasRankGE_10 : HasRankGE curve32 10 := by
  unfold curve32
  certify_curve oneTorsion 6308836808 5 "data/curve32.txt" "data/curve32-labels.txt"

/-- Curve 32 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve32.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 32. -/
public theorem curve32_j : curve32.j = 4404293641406879516329799768889980865883082988066361685849041 / 1624596034552120480493303406632087249542571198120190723072 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
