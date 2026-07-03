/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Elkies' curve has rank at least 28

This file certifies that the Mordell–Weil group of Elkies' elliptic curve

  `E : y² + xy + y = x³ - x² - 20067762415575526585033208209338542750930230312178956502 x`
  `                  + 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`

over `ℚ` has rank at least `28`, i.e. `ECCompute.HasRankGE (toCurveQ 1 (-1) 1 a₄ a₆) 28`.  This is
the 2006 rank record of N. D. Elkies (*Z²⁸ in E(ℚ), etc.*, Number Theory Listserver, May 2006),
taken from Dujella's rank-records tables; its 28 generators are all integral points.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyThree` line for line.  All numeric data is produced on the **integral short
model** `curve A₂ A₄ A₆` with `A₂ = a₁² + 4a₂ = -3`, `A₄ = 16a₄ + 8a₁a₃`, `A₆ = 64a₆ + 16a₃²` (here
`a₁ = a₃ = 1`, `a₂ = -1`), to which the general model is carried by `ModelChange.generalToShortEquiv`
(complete the square, then scale `(x, y) ↦ (4x, 8y)`, so a rational point `(x, y)` maps to
`(4x, 8y + 4x + 4)`).

* `data/rank28.txt` — the 28 points on the short model, one `x y` per line.
* `data/rank28-labels.txt` — the 28 descent columns `p θ`.
* `elkies_hasRankGE_28` — the theorem.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of Elkies' rank-28 curve (general model). -/
abbrev elkies28A₄ : ℤ := -20067762415575526585033208209338542750930230312178956502

/-- The `a₆` coefficient of Elkies' rank-28 curve (general model). -/
abbrev elkies28A₆ : ℤ :=
  34481611795030556467032985690390720374855944359319180361266008296291939448732243429

/-- Elkies' rank-28 elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - x² - 20067762415575526585033208209338542750930230312178956502 x`
  `              + 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`.

Certified to have Mordell–Weil rank at least `28` in `elkies_hasRankGE_28`. -/
def curveElkies28 : WeierstrassCurve ℚ := toCurveQ 1 (-1) 1 elkies28A₄ elkies28A₆

/-- **Elkies' curve has Mordell–Weil rank at least 28.**  Fully certified by `certify_curve`, which
computes the `28 × 28` descent-character matrix (and its `𝔽₂` inverse) from the points and labels,
then discharges every referee obligation by kernel computation: the descent characters of the 28
points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion (witnessed by the prime
`23`), so its rank over `ℚ` is at least `28`. -/
theorem elkies_hasRankGE_28 : HasRankGE curveElkies28 28 := by
  unfold curveElkies28 elkies28A₄ elkies28A₆
  certify_curve torsion 23 points "data/rank28.txt" labels "data/rank28-labels.txt"

end ECCompute
