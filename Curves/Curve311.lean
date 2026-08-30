/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 311 has rank at least 15

The elliptic curve recorded as
[curve 311](https://elliptic-rank.icarm.cloud/curve/311) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -47272342688123468294792417941461088407840527939755`   and
  `a₆ = -42941508837775730432220302570878099751385660941354601764714541918970825039`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 311 over `ℚ`. -/
@[expose] public def curve311 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -47272342688123468294792417941461088407840527939755,
    -42941508837775730432220302570878099751385660941354601764714541918970825039⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 311 has Mordell-Weil rank at least `15`. -/
public theorem curve311_hasRankGE_15 : HasRankGE curve311 15 := by
  unfold curve311
  certify_curve oneTorsion (-25464322382204490015898097) 5 "data/curve311.txt" "data/curve311-labels.txt"

/-- Curve 311 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve311.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 311. -/
public theorem curve311_j : curve311.j = 78472498277167510233267212163303516015789039131954478491136130003094465418594084807629031977312582972617614974615320510890535694407719729246678155573 / 40061623709911136587766719617560940150739066553636217227250106559640592614299091765681999638333324740367265015454841717570516045614546915381718016 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
