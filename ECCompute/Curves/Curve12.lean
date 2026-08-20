/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

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

/-- ICARM leaderboard curve 12, the Elkies-Klagsbrun rank-29 curve over `ℚ`. -/
def curve12 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -27006183241630922218434652145297453784768054621836357954737385,
    55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497⟩

/-- ICARM leaderboard curve 12 has Mordell-Weil rank at least `29`. -/
theorem curve12_hasRankGE_29 : HasRankGE curve12 29 := by
  unfold curve12
  certify_curve torsion 67 points "data/curve12.txt" labels "data/curve12-labels.txt"

end ECCompute
