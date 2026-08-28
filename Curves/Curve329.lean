/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 329 has rank at least 20

The elliptic curve recorded as
[curve 329](https://elliptic-rank.icarm.cloud/curve/329) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -16575816647974516238335754592413`   and
  `a₆ = 25996833738682985808506465614332304868873612531`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve329.txt`; descent labels are in
`data/curve329-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 329 over `ℚ`. -/
@[expose] public def curve329 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -16575816647974516238335754592413, 25996833738682985808506465614332304868873612531⟩

/-- ICARM leaderboard curve 329 has Mordell-Weil rank at least `20`. -/
public theorem curve329_hasRankGE_20 : HasRankGE curve329 20 := by
  unfold curve329
  certify_curve torsion 43 "data/curve329.txt" "data/curve329-labels.txt"

/-- Curve 329 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve329.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 329. -/
public theorem curve329_j : curve329.j = -32235060425760598610505459705183952720175912150747019539163153688769834619617429158355443721737 / 30947298446263672447906800673363399036573164907716852749726281771804104708409868257591296 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
