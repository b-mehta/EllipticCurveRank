/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

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

/-- The `a₄` coefficient of ICARM leaderboard curve 10 (general model). -/
abbrev curve10A₄ : ℚ := -120039822036992245303534619191166796374

/-- The `a₆` coefficient of ICARM leaderboard curve 10 (general model). -/
abbrev curve10A₆ : ℚ := 504224992484910670010801799168082726759443756222911415116

/-- ICARM leaderboard curve 10, the Martin-McMillen rank-24 curve over `ℚ`. -/
def curve10 : WeierstrassCurve ℚ := ⟨1, 0, 1, curve10A₄, curve10A₆⟩

/-- ICARM leaderboard curve 10 has Mordell-Weil rank at least `24`. -/
theorem curve10_hasRankGE_24 : HasRankGE curve10 24 := by
  unfold curve10 curve10A₄ curve10A₆
  certify_curve torsion 71 points "data/curve10.txt" labels "data/curve10-labels.txt"

end ECCompute
