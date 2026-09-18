/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Comparator challenge: curve 302 has rank at least 31

Trusted, independent statement of `ECCompute.curve302_hasRankGE_31` for the
[`leanprover/comparator`](https://github.com/leanprover/comparator) adversarial check.

This module carries its own copies of `curve302` and `HasRankGE`, importing only the mathlib modules
those statements need, so the statement here depends on nothing from the ECCompute development. The
`sorry` leaves the proof open; the comparator verifies that the solution module
`Curves.Curve302` proves exactly this statement, using no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`.

`curve302`, `HasRankGE`, and the target rank must be kept identical to
`Curves/Curve302.lean` and `ECCompute/MainTheorem.lean`.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 302 over `ℚ` (independent copy for the comparator challenge). -/
def curve302 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1284727764113567728281797636015784768866707681415849262157224232063,
    560368321454261339256859338901915312332769858684945406858043869199456710681989058863306170127006181⟩

/-- `HasRankGE W n` holds when `W(ℚ)` contains a finitely generated `ℤ`-submodule of free rank at
least `n` (independent copy for the comparator challenge). -/
def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∃ H : Submodule ℤ W.toAffine.Point, Module.Finite ℤ H ∧ n ≤ Module.finrank ℤ H

/-- ICARM leaderboard curve 302 has Mordell-Weil rank at least `31`. -/
theorem curve302_hasRankGE_31 : HasRankGE curve302 31 := sorry

end ECCompute
