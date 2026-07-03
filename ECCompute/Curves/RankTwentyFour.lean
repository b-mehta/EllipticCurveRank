/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Martin–McMillen curve has rank at least 24

This file certifies that the Mordell–Weil group of the Martin–McMillen elliptic curve

  `E : y² + xy + y = x³ - 120039822036992245303534619191166796374 x`
  `                  + 504224992484910670010801799168082726759443756222911415116`

over `ℚ` has rank at least `24`, i.e. `ECCompute.HasRankGE (toCurveQ 1 0 1 a₄ a₆) 24`.  This is the
2000 rank record of R. Martin and W. McMillen (*An elliptic curve over ℚ with rank at least 24*,
Number Theory Listserver, May 2000), taken from Dujella's rank-records tables.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyThree` line for line.  All numeric data is produced on the **integral short
model** `curve A₂ A₄ A₆` with `A₂ = 1`, `A₄ = 16a₄ + 8`, `A₆ = 64a₆ + 16` (here `a₁ = a₃ = 1`,
`a₂ = 0`), to which the general model is carried by `ModelChange.generalToShortEquiv` (complete the
square, then scale `(x, y) ↦ (4x, 8y)`, so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `data/rank24.txt` — the 24 points on the short model, one `x y` per line.
* `data/rank24-labels.txt` — the 24 descent columns `p θ`.
* `martinMcMillen_hasRankGE_24` — the theorem.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Martin–McMillen rank-24 curve (general model). -/
abbrev mm24A₄ : ℤ := -120039822036992245303534619191166796374

/-- The `a₆` coefficient of the Martin–McMillen rank-24 curve (general model). -/
abbrev mm24A₆ : ℤ := 504224992484910670010801799168082726759443756222911415116

/-- The Martin–McMillen rank-24 elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - 120039822036992245303534619191166796374 x`
  `              + 504224992484910670010801799168082726759443756222911415116`.

Certified to have Mordell–Weil rank at least `24` in `martinMcMillen_hasRankGE_24`. -/
def curveMartinMcMillen24 : WeierstrassCurve ℚ := toCurveQ 1 0 1 mm24A₄ mm24A₆

/-- **The Martin–McMillen curve has Mordell–Weil rank at least 24.**  Fully certified by
`certify_curve`, which computes the `24 × 24` descent-character matrix (and its `𝔽₂` inverse) from
the points and labels, then discharges every referee obligation by kernel computation: the descent
characters of the 24 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion
(witnessed by the prime `71`), so its rank over `ℚ` is at least `24`. -/
theorem martinMcMillen_hasRankGE_24 : HasRankGE curveMartinMcMillen24 24 := by
  unfold curveMartinMcMillen24 mm24A₄ mm24A₆
  certify_curve torsion 71 points "data/rank24.txt" labels "data/rank24-labels.txt"

end ECCompute
