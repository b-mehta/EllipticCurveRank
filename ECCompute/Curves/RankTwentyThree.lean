/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Martin–McMillen curve has rank at least 23 (T10)

This file is the final instantiation of ECCompute: a fully machine-checked proof that the
Mordell–Weil group of the Martin–McMillen elliptic curve

  `E : y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `                    + 32685500727716376257923347071452044295907443056345614006`

over `ℚ` has rank at least `23`, i.e. `ECCompute.HasRankGE (toCurveQ 1 0 1 a₄ a₆) 23`.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`.  All numeric
data is produced on the **integral short model** `curve 1 A₄ A₆` with
`A₄ = 16a₄ + 8` and `A₆ = 64a₆ + 16`, to which the general model is carried by the group
isomorphism `ModelChange.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`,
so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `data/rank23.txt` — the 23 points on the short model, one `x y` per line, with each coordinate an
  integer or a reduced fraction `a/b`.  (`certify_curve` emits fractional `x`-coordinates in reduced
  `Rat.mk'` form so the kernel evaluates on them by `rfl`.)
* `data/rank23-labels.txt` — the 23 descent columns `p θ`, primes between `7` and `163`, following
  Cremona's worked example (§2.3 of *On the computation of Mordell–Weil and 2-Selmer groups*).
* `martinMcMillen_hasRankGE_23` — the theorem.  The `certify_curve` tactic reads the points and
  labels from those files, computes the `23 × 23` descent-character matrix over `𝔽₂` (and its
  inverse), assembles the certificate, and transports the bound to the general model.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- The `a₄` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₄ : ℤ := -19252966408674012828065964616418441723

/-- The `a₆` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₆ : ℤ := 32685500727716376257923347071452044295907443056345614006


/-- The Martin–McMillen elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `              + 32685500727716376257923347071452044295907443056345614006`.

Certified to have Mordell–Weil rank at least `23` in `martinMcMillen_hasRankGE_23`. -/
def curveMartinMcMillen : WeierstrassCurve ℚ := toCurveQ 1 0 1 mmA₄ mmA₆

/-- **The Martin–McMillen curve has Mordell–Weil rank at least 23.**  Fully certified by
`certify_curve`, which computes the `23 × 23` descent-character matrix (and its `𝔽₂` inverse) from
the points and labels, then discharges every referee obligation by kernel computation: the descent
characters of the 23 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion
(witnessed by the prime `29`), so its rank over `ℚ` is at least `23`. -/
theorem martinMcMillen_hasRankGE_23 : HasRankGE curveMartinMcMillen 23 := by
  unfold curveMartinMcMillen mmA₄ mmA₆
  certify_curve torsion 29 points "data/rank23.txt" labels "data/rank23-labels.txt"

end ECCompute
