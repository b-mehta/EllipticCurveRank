/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 380 has rank at least 18

The elliptic curve recorded as
[curve 380](https://elliptic-rank.icarm.cloud/curve/380) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -5976631508664466981686244`   and
  `a₆ = 4880007354067700108548264545546534926`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve380.txt`; descent labels are in
`data/curve380-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 380 over `ℚ`. -/
@[expose] public def curve380 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -5976631508664466981686244, 4880007354067700108548264545546534926⟩

/-- ICARM leaderboard curve 380 has Mordell-Weil rank at least `18`. -/
public theorem curve380_hasRankGE_18 : HasRankGE curve380 18 := by
  unfold curve380
  certify_curve torsion 17 "data/curve380.txt" "data/curve380-labels.txt"

/-- Curve 380 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve380.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 380. -/
public theorem curve380_j : curve380.j = 23609845893926943555065843408902957320187872636320744888622956964649538483139769 / 3375253455561014613462251472724013716887400077887837382135225875155809632100 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
