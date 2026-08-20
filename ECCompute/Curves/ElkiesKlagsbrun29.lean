/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# The Elkies-Klagsbrun curve has rank at least 29

The Elkies-Klagsbrun elliptic curve

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -27006183241630922218434652145297453784768054621836357954737385`   and
  `a₆ = 5525805855134237647573669959111819182152106703253507960837240477`
  `     9149413277716173425636721497`

over `ℚ` has Mordell-Weil rank at least `29`, a rank record of N. D. Elkies and Z. Klagsbrun. Points
in `data/elkiesKlagsbrun29.txt`, descent labels in `data/elkiesKlagsbrun29-labels.txt` (primes `19`
to `179`); `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The Elkies-Klagsbrun rank-29 elliptic curve over `ℚ`. Certified rank ≥ 29 in
`curveElkiesKlagsbrun29_hasRankGE_29`. -/
def curveElkiesKlagsbrun29 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -27006183241630922218434652145297453784768054621836357954737385,
    55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497⟩

/-- The Elkies-Klagsbrun curve has Mordell-Weil rank at least `29`. -/
theorem curveElkiesKlagsbrun29_hasRankGE_29 : HasRankGE curveElkiesKlagsbrun29 29 := by
  unfold curveElkiesKlagsbrun29
  certify_curve torsion 67 points "data/elkiesKlagsbrun29.txt"
    labels "data/elkiesKlagsbrun29-labels.txt"

end ECCompute
