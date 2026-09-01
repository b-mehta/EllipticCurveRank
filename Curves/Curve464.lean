/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 464 has rank at least 20

The elliptic curve recorded as
[curve 464](https://elliptic-rank.icarm.cloud/curve/464) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -35401605264465213409496277503084042915`   and
  `a₆ = 80481020268953308189156706852613645754737587637675825921`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 464 over `ℚ`. -/
@[expose] public def curve464 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -35401605264465213409496277503084042915,
    80481020268953308189156706852613645754737587637675825921⟩

/-- ICARM leaderboard curve 464 has Mordell-Weil rank at least `20`. -/
public theorem curve464_hasRankGE_20 : HasRankGE curve464 20 := by
  unfold curve464
  certify_curve torsion 23 "data/curve464.txt" "data/curve464-labels.txt"

/-- Curve 464 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve464.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 464. -/
public theorem curve464_j : curve464.j = 32929134425127092344895928090888929672502436915556255972104510202933503729434926544702920818754915874318043 / 277818763790998875752879529202831351097810299377234254613037007806524918278064956717048035653732089856 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
