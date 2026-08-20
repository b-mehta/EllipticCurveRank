/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Check.JInvariant

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

/-- Curve 12 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve12.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 12. -/
theorem curve12_j : curve12.j = -2178278186417661901253576189103582365997935396472623778840162578414756885078160008166998745534482953456950649575682874999212260264866779577866068298184392291373758903459432104260760768986641 / 58514056884179895803252795545068205623215359270190478217393508483140281138663769634024489915971980794469429246265449489823479442097938729025702174957426421151737866434992604323840000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
