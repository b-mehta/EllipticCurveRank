/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 38 has rank at least 18

The elliptic curve recorded as
[curve 38](https://elliptic-rank.icarm.cloud/curve/38) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -26175960092705884096311701787701203903556438969515`   and
  `a₆ = 51069381476131486489742177100373772089779103253890567848326775119094885041`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 38 over `ℚ`. -/
@[expose] public def curve038 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -26175960092705884096311701787701203903556438969515,
    51069381476131486489742177100373772089779103253890567848326775119094885041⟩

/-- ICARM leaderboard curve 38 has Mordell-Weil rank at least `18`. -/
public theorem curve038_hasRankGE_18 : HasRankGE curve038 18 := by
  unfold curve038
  certify_curve oneTorsion 12732161191102245007949048 5 "data/curve038.txt" "data/curve038-labels.txt"

/-- Curve 38 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve038.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 38. -/
public theorem curve038_j : curve038.j = 13323059362590002593299168845444130391705189385152573903874739428631849797263905708539525584729853042496428109120258334733841162904613294558121181493 / 142169832701772977718561293984707384280114726482259092666685743596875256155267836859249376913473187810947611641871603576022969816446693834489856 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
