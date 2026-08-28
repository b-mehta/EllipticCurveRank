/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 179 has rank at least 16

The elliptic curve recorded as
[curve 179](https://elliptic-rank.icarm.cloud/curve/179) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -5156525671696520871642`   and
  `a₆ = 143887580422027574095483236694887`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve179.txt`; descent labels are in
`data/curve179-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 179 over `ℚ`. -/
@[expose] public def curve179 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -5156525671696520871642, 143887580422027574095483236694887⟩

/-- ICARM leaderboard curve 179 has Mordell-Weil rank at least `16`. -/
public theorem curve179_hasRankGE_16 : HasRankGE curve179 16 := by
  unfold curve179
  certify_curve torsion 5 "data/curve179.txt" "data/curve179-labels.txt"

/-- Curve 179 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve179.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 179. -/
public theorem curve179_j : curve179.j = -15163353677476126224985610107966391657812097927904436371419440123684513 / 168881732015251142870523473594217561643594320461409532628190621696 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
