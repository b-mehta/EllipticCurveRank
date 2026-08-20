/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# Curve 7 has rank at least 20

The elliptic curve recorded as
[curve 7](https://elliptic-rank.icarm.cloud/curve/7) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - 431092980766333677958362095891166 x`
  `              + 5156283555366643659035652799871176909391533088196`

over `ℚ`. It has Mordell-Weil rank at least `20`, the 1993 rank record of K. Nagao. Points in
`data/curve7.txt`, descent labels in `data/curve7-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 7, Nagao's rank-20 curve over `ℚ`. -/
def curve7 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -431092980766333677958362095891166, 5156283555366643659035652799871176909391533088196⟩

/-- ICARM leaderboard curve 7 has Mordell-Weil rank at least `20`. -/
theorem curve7_hasRankGE_20 : HasRankGE curve7 20 := by
  unfold curve7
  certify_curve torsion 23 points "data/curve7.txt" labels "data/curve7-labels.txt"

end ECCompute
