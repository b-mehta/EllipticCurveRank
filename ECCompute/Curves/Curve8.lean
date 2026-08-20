/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 8 has rank at least 22

The elliptic curve recorded as
[curve 8](https://elliptic-rank.icarm.cloud/curve/8) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - 940299517776391362903023121165864 x`
  `                  + 10707363070719743033425295515449274534651125011362`

over `ℚ`. It has Mordell-Weil rank at least `22`, the 1997 rank record of S. Fermigier. Points in
`data/curve8.txt`, descent labels in `data/curve8-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of ICARM leaderboard curve 8 (general model). -/
abbrev curve8A₄ : ℚ := -940299517776391362903023121165864

/-- The `a₆` coefficient of ICARM leaderboard curve 8 (general model). -/
abbrev curve8A₆ : ℚ := 10707363070719743033425295515449274534651125011362

/-- ICARM leaderboard curve 8, Fermigier's rank-22 curve over `ℚ`. -/
def curve8 : WeierstrassCurve ℚ := ⟨1, 0, 1, curve8A₄, curve8A₆⟩

/-- ICARM leaderboard curve 8 has Mordell-Weil rank at least `22`. -/
theorem curve8_hasRankGE_22 : HasRankGE curve8 22 := by
  unfold curve8 curve8A₄ curve8A₆
  certify_curve torsion 31 points "data/curve8.txt" labels "data/curve8-labels.txt"

end ECCompute
