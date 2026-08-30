/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 331 has rank at least 19

The elliptic curve recorded as
[curve 331](https://elliptic-rank.icarm.cloud/curve/331) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -19765899815999953792466328892`   and
  `a₆ = 930706389260018051001267482454403054915180`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 331 over `ℚ`. -/
@[expose] public def curve331 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -19765899815999953792466328892, 930706389260018051001267482454403054915180⟩

/-- ICARM leaderboard curve 331 has Mordell-Weil rank at least `19`. -/
public theorem curve331_hasRankGE_19 : HasRankGE curve331 19 := by
  unfold curve331
  certify_curve torsion 37 "data/curve331.txt" "data/curve331-labels.txt"

/-- Curve 331 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve331.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 331. -/
public theorem curve331_j : curve331.j = 854030697829260082556902220633116012266776148135418838408206407553210432379733471540421321 / 120026114450375268731550080313050637490976047007792951958607127362398246018745515426132 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
