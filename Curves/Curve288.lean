/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 288 has rank at least 1

The elliptic curve recorded as
[curve 288](https://elliptic-rank.icarm.cloud/curve/288) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -121983437484123355137076665142508763913498826398414875780808033937915968094`
  `     30161`   and
  `a₆ = -163983221857943604956790618267997694895328277408167744063646212102427035034`
  `     93389262182826887092729077867268914628835439`

over `ℚ`. It has Mordell-Weil rank at least `1`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve288.txt`; descent labels are in
`data/curve288-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 288 over `ℚ`. -/
@[expose] public def curve288 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -12198343748412335513707666514250876391349882639841487578080803393791596809430161,
    -16398322185794360495679061826799769489532827740816774406364621210242703503493389262182826887092729077867268914628835439⟩

/-- ICARM leaderboard curve 288 has Mordell-Weil rank at least `1`. -/
public theorem curve288_hasRankGE_1 : HasRankGE curve288 1 := by
  unfold curve288
  certify_curve fullTorsion "data/curve288.txt" "data/curve288-labels.txt"

/-- Curve 288 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve288.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 288. -/
public theorem curve288_j : curve288.j = 12251982718821576467938232137419615856450169346205768450404750732160073718103551353369414093487513687654659955393294656854325223474378232932824365892939680078005157562571990922452411019808112694303171205031744834012377984864410825455024976 / 5231235593124503021798387747698599390366604339837522119086723762384537953562339849435664623559518811517825887365561725579894183461730599296452818090372104025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
