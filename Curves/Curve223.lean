/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 223 has rank at least 18

The elliptic curve recorded as
[curve 223](https://elliptic-rank.icarm.cloud/curve/223) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -13827291580782875260211544`   and
  `a₆ = 19952277912018354390476665828916413300`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 223 over `ℚ`. -/
@[expose] public def curve223 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -13827291580782875260211544, 19952277912018354390476665828916413300⟩

/-- ICARM leaderboard curve 223 has Mordell-Weil rank at least `18`. -/
public theorem curve223_hasRankGE_18 : HasRankGE curve223 18 := by
  unfold curve223
  certify_curve torsion 29 "data/curve223.txt" "data/curve223-labels.txt"

/-- Curve 223 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve223.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 223. -/
public theorem curve223_j : curve223.j = -401058335438813143213971079227539137282297678323233972078130987443011574683009 / 3813252252629096528179660181276040684149024921496063243047757455898622500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
