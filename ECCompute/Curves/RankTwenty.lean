/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Nagao's curve has rank at least 20

This file certifies that the Mordell–Weil group of Nagao's elliptic curve

  `E : y² + xy = x³ - 431092980766333677958362095891166 x`
  `              + 5156283555366643659035652799871176909391533088196`

over `ℚ` has rank at least `20`, i.e. `ECCompute.HasRankGE (toCurveQ 1 0 0 a₄ a₆) 20`.  This is
the 1993 rank record of K. Nagao (*An example of elliptic curve over ℚ with rank ≥ 20*, Proc. Japan
Acad. Ser. A Math. Sci. **69** (1993), 291–293), taken from Dujella's rank-records tables.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyNine` line for line.  All numeric data is produced on the **integral short
model** `curve A₂ A₄ A₆` with `A₂ = 1`, `A₄ = 16a₄`, `A₆ = 64a₆` (here `a₁ = 1`, `a₂ = a₃ = 0`), to
which the general model is carried by `ModelChange.generalToShortEquiv` (complete the square, then
scale `(x, y) ↦ (4x, 8y)`, so a rational point `(x, y)` maps to `(4x, 8y + 4x)`).

* `data/rank20.txt` — the 20 points on the short model, one `x y` per line.
* `data/rank20-labels.txt` — the 20 descent columns `p θ`.
* `nagao_hasRankGE_20` — the theorem.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of Nagao's rank-20 curve (general model). -/
abbrev nagao20A₄ : ℤ := -431092980766333677958362095891166

/-- The `a₆` coefficient of Nagao's rank-20 curve (general model). -/
abbrev nagao20A₆ : ℤ := 5156283555366643659035652799871176909391533088196

/-- Nagao's rank-20 elliptic curve over `ℚ` (general model)

  `y² + xy = x³ - 431092980766333677958362095891166 x`
  `          + 5156283555366643659035652799871176909391533088196`.

Certified to have Mordell–Weil rank at least `20` in `nagao_hasRankGE_20`. -/
def curveNagao20 : WeierstrassCurve ℚ := toCurveQ 1 0 0 nagao20A₄ nagao20A₆

/-- **Nagao's curve has Mordell–Weil rank at least 20.**  Fully certified by `certify_curve`, which
computes the `20 × 20` descent-character matrix (and its `𝔽₂` inverse) from the points and labels,
then discharges every referee obligation by kernel computation: the descent characters of the 20
points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion (witnessed by the prime
`23`), so its rank over `ℚ` is at least `20`. -/
theorem nagao_hasRankGE_20 : HasRankGE curveNagao20 20 := by
  unfold curveNagao20 nagao20A₄ nagao20A₆
  certify_curve torsion 23 points "data/rank20.txt" labels "data/rank20-labels.txt"

end ECCompute
