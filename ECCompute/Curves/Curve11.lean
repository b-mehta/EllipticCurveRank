/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 11 has rank at least 28

The elliptic curve recorded as
[curve 11](https://elliptic-rank.icarm.cloud/curve/11) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -20067762415575526585033208209338542750930230312178956502`   and
  `a₆ = 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`

over `ℚ`. It has Mordell-Weil rank at least `28`, the 2006 rank record of N. D. Elkies. Points in
`data/curve11.txt`, descent labels in `data/curve11-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of ICARM leaderboard curve 11 (general model). -/
abbrev curve11A₄ : ℚ := -20067762415575526585033208209338542750930230312178956502

/-- The `a₆` coefficient of ICARM leaderboard curve 11 (general model). -/
abbrev curve11A₆ : ℚ :=
  34481611795030556467032985690390720374855944359319180361266008296291939448732243429

/-- ICARM leaderboard curve 11, Elkies' rank-28 curve over `ℚ`. -/
def curve11 : WeierstrassCurve ℚ := ⟨1, -1, 1, curve11A₄, curve11A₆⟩

/-- ICARM leaderboard curve 11 has Mordell-Weil rank at least `28`. -/
theorem curve11_hasRankGE_28 : HasRankGE curve11 28 := by
  unfold curve11 curve11A₄ curve11A₆
  certify_curve torsion 23 points "data/curve11.txt" labels "data/curve11-labels.txt"

end ECCompute
