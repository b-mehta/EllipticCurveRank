/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 9 has rank at least 23

The elliptic curve recorded as
[curve 9](https://elliptic-rank.icarm.cloud/curve/9) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `                    + 32685500727716376257923347071452044295907443056345614006`

over `ℚ`. It has Mordell-Weil rank at least `23`, a curve of R. Martin and W. McMillen. Points in
`data/curve9.txt`, descent labels in `data/curve9-labels.txt` (primes `7` to `163`, from §2.3 of
Cremona's *On the computation of Mordell-Weil and 2-Selmer groups*); `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 9, a Martin-McMillen curve over `ℚ`. -/
def curve9 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -19252966408674012828065964616418441723,
    32685500727716376257923347071452044295907443056345614006⟩

/-- ICARM leaderboard curve 9 has Mordell-Weil rank at least `23`. -/
theorem curve9_hasRankGE_23 : HasRankGE curve9 23 := by
  unfold curve9
  certify_curve torsion 29 points "data/curve9.txt" labels "data/curve9-labels.txt"

end ECCompute
