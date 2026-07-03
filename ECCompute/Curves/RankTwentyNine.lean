/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# A second curve of rank at least 29

This file is a second full instantiation of ECCompute: a machine-checked proof that the
Mordell–Weil group of the elliptic curve

  `E : y² + xy = x³ + a₄ x + a₆`

over `ℚ` (with the large integer coefficients `a₄`, `a₆` below) has rank at least `29`, i.e.
`ECCompute.HasRankGE (toCurveQ 1 0 0 a₄ a₆) 29`.

The proof is a descent-character certificate in the sense of `ECCompute.MainTheorem`, following
`ECCompute.RankTwentyThree` line for line. All numeric data is produced on the **integral short
model** `curve 1 A₄ A₆` with `A₄ = 16a₄` and `A₆ = 64a₆` (here `a₁ = 1`, `a₂ = a₃ = 0`, so the
`b`-invariant shifts vanish), to which the general model is carried by the group isomorphism
`ModelChange.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`, so a
rational point `(x, y)` maps to `(4x, 8y + 4x)`).

* `data/rank29.txt` — the 29 points on the short model, one `x y` per line, with each coordinate an
  integer or a reduced fraction `a/b`.  (`certify_curve` emits the one fractional `x`-coordinate in
  reduced `Rat.mk'` form so the kernel evaluates on it by `rfl`.)
* `data/rank29-labels.txt` — the 29 descent columns `p θ`, primes between `19` and `179`, matching
  Cremona's descent-image output for this curve.
* `elkiesKlagsbrun_hasRankGE_29` — the theorem.  The `certify_curve` tactic reads the points and
  labels from those files, computes the `29 × 29` descent-character matrix over `𝔽₂` (and its
  inverse), assembles the certificate, and transports the bound to the general model.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

-- The `rfl` certificate checks (`checkInv`, the `matB` entries) reduce large `Nat` recursions in
-- the elaborator, so raise the recursion limit for the whole file.
set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₄ : ℤ := -27006183241630922218434652145297453784768054621836357954737385

/-- The `a₆` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₆ : ℤ :=
  55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- The Elkies–Klagsbrun rank-29 elliptic curve over `ℚ` (general model)

  `y² + xy = x³ + ekA₄ x + ekA₆`.

Certified to have Mordell–Weil rank at least `29` in `elkiesKlagsbrun_hasRankGE_29`. -/
def curveElkiesKlagsbrun : WeierstrassCurve ℚ := toCurveQ 1 0 0 ekA₄ ekA₆

/-- **The Elkies–Klagsbrun curve has Mordell–Weil rank at least 29.**  Fully certified by
`certify_curve`, which computes the `29 × 29` descent-character matrix (and its `𝔽₂` inverse) from
the points and labels, then discharges every referee obligation by kernel computation: the descent
characters of the 29 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion
(witnessed by the prime `67`), so its rank over `ℚ` is at least `29`. -/
theorem elkiesKlagsbrun_hasRankGE_29 : HasRankGE curveElkiesKlagsbrun 29 := by
  unfold curveElkiesKlagsbrun ekA₄ ekA₆
  certify_curve torsion 67 points "data/rank29.txt" labels "data/rank29-labels.txt"

end ECCompute
