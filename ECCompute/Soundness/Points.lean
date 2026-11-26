/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import ECCompute.Soundness.Fold

/-!
# Soundness of the point-on-curve check

`checkPoints_iff` shows that the kernel check `ECCompute.checkPoints` (from `Kernel`) over the flat
point encoding `(xnA, xs, xd, ynA, yd)` holds exactly when every decoded point satisfies the affine
Weierstrass equation of the short model `curveQ a₂ a₄ a₆` and is in lowest terms. (Measurement
branch: the soundness proof for the flat encoding is deferred.)
-/

namespace ECCompute

open WeierstrassCurve

variable {a₂ a₄ a₆ : ℤ}

/-- The rational coordinate `(xnA, xs, xd)` of a flat point: magnitude `xnA`, sign `xs`
(`true` = negative), denominator `xd`. -/
public noncomputable def flatCoord (xnA : ℕ) (xs : Bool) (xd : ℕ) : ℚ :=
  (if xs then -(xnA : ℚ) else (xnA : ℚ)) / (xd : ℚ)

/-- `checkPoints` over the flat encoding holds iff every decoded point satisfies the short-model
equation. -/
public theorem checkPoints_iff {pts : List (ℕ × Bool × ℕ × ℕ × ℕ)} :
    checkPoints a₂ a₄ a₆ pts ↔ ∀ p ∈ pts,
      (curveQ a₂ a₄ a₆).toAffine.Equation (flatCoord p.1 p.2.1 p.2.2.1)
        (flatCoord p.2.2.2.1 false p.2.2.2.2) := by
  sorry

end ECCompute
