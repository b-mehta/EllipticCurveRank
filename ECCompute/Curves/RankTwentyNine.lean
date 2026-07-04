/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# A second curve of rank at least 29

This file certifies that the elliptic curve `E : y² + xy = x³ + a₄ x + a₆` over `ℚ` (with the large
integer coefficients `a₄`, `a₆` below) has Mordell-Weil rank at least `29`, a descent-character
certificate in the sense of `ECCompute.MainTheorem`.

* `data/rank29.txt`: the 29 points on the short model, one `x y` per line, each coordinate an
  integer or a reduced fraction `a/b`.
* `data/rank29-labels.txt`: the 29 descent columns `p θ`, primes between `19` and `179`, matching
  Cremona's descent-image output for this curve.

`certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

-- The `rfl` certificate checks (`checkInv`, the `matB` entries) reduce large `Nat` recursions in
-- the elaborator, so raise the recursion limit for the whole file.
set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Elkies-Klagsbrun rank-29 curve (general model). -/
abbrev ekA₄ : ℤ := -27006183241630922218434652145297453784768054621836357954737385

/-- The `a₆` coefficient of the Elkies-Klagsbrun rank-29 curve (general model). -/
abbrev ekA₆ : ℤ :=
  55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- The Elkies-Klagsbrun rank-29 elliptic curve over `ℚ` (general model).  Certified to have
Mordell-Weil rank at least `29` in `elkiesKlagsbrun_hasRankGE_29`. -/
def curveElkiesKlagsbrun : WeierstrassCurve ℚ := toCurveQ 1 0 0 ekA₄ ekA₆

/-- The Elkies-Klagsbrun curve has Mordell-Weil rank at least `29`. -/
theorem elkiesKlagsbrun_hasRankGE_29 : HasRankGE curveElkiesKlagsbrun 29 := by
  unfold curveElkiesKlagsbrun ekA₄ ekA₆
  certify_curve torsion 67 points "data/rank29.txt" labels "data/rank29-labels.txt"

end ECCompute
