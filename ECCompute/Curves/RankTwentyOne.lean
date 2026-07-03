/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Nagao–Kouya curve has rank at least 21

This file certifies that the Mordell–Weil group of the Nagao–Kouya elliptic curve

  `E : y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `                  - 19474361277787151947255961435459054151501792241320535`

over `ℚ` has rank at least `21`, i.e. `ECCompute.HasRankGE (toCurveQ 1 1 1 a₄ a₆) 21`.  This is the
1994 rank record of K. Nagao and T. Kouya (*An example of elliptic curve over ℚ with rank ≥ 21*,
Proc. Japan Acad. Ser. A Math. Sci. **70** (1994), 104–105), taken from Dujella's rank-records
tables.  Three of the 21 generators listed there contain transcription typos; the values used here
are corrected against the Nagao–Kouya original.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyThree` line for line.  All numeric data is produced on the **integral short
model** `curve A₂ A₄ A₆` with `A₂ = 5`, `A₄ = 16a₄ + 8`, `A₆ = 64a₆ + 16` (here `a₁ = a₂ = a₃ = 1`),
to which the general model is carried by `ModelChange.generalToShortEquiv` (complete the square, then
scale `(x, y) ↦ (4x, 8y)`, so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `data/rank21.txt` — the 21 points on the short model, one `x y` per line.
* `data/rank21-labels.txt` — the 21 descent columns `p θ`.
* `nagaoKouya_hasRankGE_21` — the theorem.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Nagao–Kouya rank-21 curve (general model). -/
abbrev nk21A₄ : ℤ := -215843772422443922015169952702159835

/-- The `a₆` coefficient of the Nagao–Kouya rank-21 curve (general model). -/
abbrev nk21A₆ : ℤ := -19474361277787151947255961435459054151501792241320535

/-- The Nagao–Kouya rank-21 elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `              - 19474361277787151947255961435459054151501792241320535`.

Certified to have Mordell–Weil rank at least `21` in `nagaoKouya_hasRankGE_21`. -/
def curveNagaoKouya21 : WeierstrassCurve ℚ := toCurveQ 1 1 1 nk21A₄ nk21A₆

/-- **The Nagao–Kouya curve has Mordell–Weil rank at least 21.**  Fully certified by `certify_curve`,
which computes the `21 × 21` descent-character matrix (and its `𝔽₂` inverse) from the points and
labels, then discharges every referee obligation by kernel computation: the descent characters of
the 21 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion (witnessed by
the prime `11`), so its rank over `ℚ` is at least `21`. -/
theorem nagaoKouya_hasRankGE_21 : HasRankGE curveNagaoKouya21 21 := by
  unfold curveNagaoKouya21 nk21A₄ nk21A₆
  certify_curve torsion 11 points "data/rank21.txt" labels "data/rank21-labels.txt"

end ECCompute
