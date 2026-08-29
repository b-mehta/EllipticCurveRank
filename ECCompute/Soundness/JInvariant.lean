/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.ForMathlib.WeierstrassCurve

/-!
# The j-invariant certification lemmas

`WeierstrassCurve.j_eq_iff` and `WeierstrassCurve.isElliptic_of_Δ_ne_zero` live in
`ECCompute.ForMathlib.WeierstrassCurve`. This module re-exports them for the generated `Curves/`
files, which `open WeierstrassCurve` and reference the lemmas unqualified.
-/
