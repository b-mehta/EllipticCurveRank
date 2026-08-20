/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Check.JInvariant

/-!
# Curve 10 has rank at least 24

The elliptic curve recorded as
[curve 10](https://elliptic-rank.icarm.cloud/curve/10) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - 120039822036992245303534619191166796374 x`
  `                  + 504224992484910670010801799168082726759443756222911415116`

over `ℚ`. It has Mordell-Weil rank at least `24`, the 2000 rank record of R. Martin and W. McMillen.
Points in `data/curve10.txt`, descent labels in `data/curve10-labels.txt`; `certify_curve` does the
rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 10, the Martin-McMillen rank-24 curve over `ℚ`. -/
def curve10 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -120039822036992245303534619191166796374,
    504224992484910670010801799168082726759443756222911415116⟩

/-- ICARM leaderboard curve 10 has Mordell-Weil rank at least `24`. -/
theorem curve10_hasRankGE_24 : HasRankGE curve10 24 := by
  unfold curve10
  certify_curve torsion 71 points "data/curve10.txt" labels "data/curve10-labels.txt"

/-- Curve 10 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve10.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 10. -/
theorem curve10_j : curve10.j = 191293291886905749650630022503662748397674588260823851486195145279492706081449931917775375694299848445871423382967440089 / 869228312577660772590804276974894693796770087691229179004716529760427780748163030521421801352204521776094281605900 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
