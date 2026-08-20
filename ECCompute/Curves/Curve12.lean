/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 12 has rank at least 29

The elliptic curve recorded as
[curve 12](https://elliptic-rank.icarm.cloud/curve/12) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -27006183241630922218434652145297453784768054621836357954737385`   and
  `a₆ = 5525805855134237647573669959111819182152106703253507960837240477`
  `     9149413277716173425636721497`

over `ℚ`. It has Mordell-Weil rank at least `29`, a rank record of N. D. Elkies and Z. Klagsbrun.
Points in `data/curve12.txt`, descent labels in `data/curve12-labels.txt` (primes `19` to `179`);
`certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of ICARM leaderboard curve 12 (general model). -/
abbrev curve12A₄ : ℚ := -27006183241630922218434652145297453784768054621836357954737385

/-- The `a₆` coefficient of ICARM leaderboard curve 12 (general model). -/
abbrev curve12A₆ : ℚ :=
  55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- ICARM leaderboard curve 12, the Elkies-Klagsbrun rank-29 curve over `ℚ`. -/
def curve12 : WeierstrassCurve ℚ := ⟨1, 0, 0, curve12A₄, curve12A₆⟩

/-- ICARM leaderboard curve 12 has Mordell-Weil rank at least `29`. -/
theorem curve12_hasRankGE_29 : HasRankGE curve12 29 := by
  unfold curve12 curve12A₄ curve12A₆
  certify_curve torsion 67 points "data/curve12.txt" labels "data/curve12-labels.txt"

end ECCompute
