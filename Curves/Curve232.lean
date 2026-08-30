/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 232 has rank at least 17

The elliptic curve recorded as
[curve 232](https://elliptic-rank.icarm.cloud/curve/232) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -31972892142603899925`   and
  `a₆ = 73862336294883442290824915625`

over `ℚ`. It has Mordell-Weil rank at least `17`.

Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 232 over `ℚ`. -/
@[expose] public def curve232 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -31972892142603899925, 73862336294883442290824915625⟩

/-- ICARM leaderboard curve 232 has Mordell-Weil rank at least `17`. -/
public theorem curve232_hasRankGE_17 : HasRankGE curve232 17 := by
  unfold curve232
  certify_curve torsion 7 "data/curve232.txt" "data/curve232-labels.txt"

/-- Curve 232 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve232.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 232. -/
public theorem curve232_j : curve232.j = -231339319632341197502553322693331164389336635357469411411793 / 16960744270682733987898811772991882124380855242719744844 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
