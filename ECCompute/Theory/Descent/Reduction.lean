/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.IntModel
import ECCompute.Theory.Descent.Reduction.Repr
import ECCompute.Theory.Descent.Reduction.Def
import ECCompute.Theory.Descent.Reduction.Hom
import ECCompute.Theory.Descent.Reduction.EpsFinite

/-!
# Reduction of the integral model modulo `p`

Aggregator for the `Reduction` subdirectory, which builds the reduction map from the integral
Weierstrass model to the curve over `𝔽ₚ` and establishes its additivity:

* `Reduction.IntModel`: the integral model of the descent curve.
* `Reduction.Repr`: the integer projective representative of an affine point.
* `Reduction.Def`: the reduction map on affine points.
* `Reduction.Hom`: additivity of the reduction map.
* `Reduction.EpsFinite`: the finite-field descent character `εp_finite` and its additivity.
-/
