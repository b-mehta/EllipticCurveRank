/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Fermigier's curve has rank at least 22

This file certifies that the Mordell–Weil group of Fermigier's elliptic curve

  `E : y² + xy + y = x³ - 940299517776391362903023121165864 x`
  `                  + 10707363070719743033425295515449274534651125011362`

over `ℚ` has rank at least `22`, i.e. `ECCompute.HasRankGE (toCurveQ 1 0 1 a₄ a₆) 22`.  This is the
1997 rank record of S. Fermigier (*Une courbe elliptique définie sur ℚ de rang ≥ 22*, Acta Arith.
(1997), 359–363), taken from Dujella's rank-records tables.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyThree` line for line.  All numeric data is produced on the **integral short
model** `curve A₂ A₄ A₆` with `A₂ = 1`, `A₄ = 16a₄ + 8`, `A₆ = 64a₆ + 16` (here `a₁ = a₃ = 1`,
`a₂ = 0`), to which the general model is carried by `ModelChange.generalToShortEquiv` (complete the
square, then scale `(x, y) ↦ (4x, 8y)`, so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `data/rank22.txt` — the 22 points on the short model, one `x y` per line.
* `data/rank22-labels.txt` — the 22 descent columns `p θ`.
* `fermigier_hasRankGE_22` — the theorem.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of Fermigier's rank-22 curve (general model). -/
abbrev fermigier22A₄ : ℤ := -940299517776391362903023121165864

/-- The `a₆` coefficient of Fermigier's rank-22 curve (general model). -/
abbrev fermigier22A₆ : ℤ := 10707363070719743033425295515449274534651125011362

/-- Fermigier's rank-22 elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - 940299517776391362903023121165864 x`
  `              + 10707363070719743033425295515449274534651125011362`.

Certified to have Mordell–Weil rank at least `22` in `fermigier_hasRankGE_22`. -/
def curveFermigier22 : WeierstrassCurve ℚ := toCurveQ 1 0 1 fermigier22A₄ fermigier22A₆

/-- **Fermigier's curve has Mordell–Weil rank at least 22.**  Fully certified by `certify_curve`,
which computes the `22 × 22` descent-character matrix (and its `𝔽₂` inverse) from the points and
labels, then discharges every referee obligation by kernel computation: the descent characters of
the 22 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion (witnessed by
the prime `31`), so its rank over `ℚ` is at least `22`. -/
theorem fermigier_hasRankGE_22 : HasRankGE curveFermigier22 22 := by
  unfold curveFermigier22 fermigier22A₄ fermigier22A₆
  certify_curve torsion 31 points "data/rank22.txt" labels "data/rank22-labels.txt"

end ECCompute
