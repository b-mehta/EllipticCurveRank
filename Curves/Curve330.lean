/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 330 has rank at least 19

The elliptic curve recorded as
[curve 330](https://elliptic-rank.icarm.cloud/curve/330) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -482886126837705164255195633736`   and
  `a₆ = 128875500361225289360623432042214069669747136`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 330 over `ℚ`. -/
@[expose] public def curve330 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -482886126837705164255195633736, 128875500361225289360623432042214069669747136⟩

/-- ICARM leaderboard curve 330 has Mordell-Weil rank at least `19`. -/
public theorem curve330_hasRankGE_19 : HasRankGE curve330 19 := by
  unfold curve330
  certify_curve torsion 29 "data/curve330.txt" "data/curve330-labels.txt"

/-- Curve 330 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve330.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 330. -/
public theorem curve330_j : curve330.j = 12160682249692098319588156233563740596787144380450135608207304325054010532869107794015489316 / 30554450888584242786872177034566167206109893576281438157362516501526369675685058094525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
