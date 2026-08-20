/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 74 has rank at least 21

The elliptic curve recorded as
[curve 74](https://elliptic-rank.icarm.cloud/curve/74) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `                  - 19474361277787151947255961435459054151501792241320535`

over `ℚ`. It has Mordell-Weil rank at least `21`, the 1994 rank record of K. Nagao and T. Kouya.
Points in `data/curve74.txt`, descent labels in `data/curve74-labels.txt`; `certify_curve` does the
rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of ICARM leaderboard curve 74 (general model). -/
abbrev curve74A₄ : ℚ := -215843772422443922015169952702159835

/-- The `a₆` coefficient of ICARM leaderboard curve 74 (general model). -/
abbrev curve74A₆ : ℚ := -19474361277787151947255961435459054151501792241320535

/-- ICARM leaderboard curve 74, the Nagao-Kouya rank-21 curve over `ℚ`. -/
def curve74 : WeierstrassCurve ℚ := ⟨1, 1, 1, curve74A₄, curve74A₆⟩

/-- ICARM leaderboard curve 74 has Mordell-Weil rank at least `21`. -/
theorem curve74_hasRankGE_21 : HasRankGE curve74 21 := by
  unfold curve74 curve74A₄ curve74A₆
  certify_curve torsion 11 points "data/curve74.txt" labels "data/curve74-labels.txt"

end ECCompute
