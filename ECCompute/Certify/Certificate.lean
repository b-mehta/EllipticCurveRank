/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Rat.Defs
import ECCompute.Check.F2Invert

/-!
# The rank-bound certificate data type

`ECCompute.Certificate` bundles the data a referee audits to accept a lower bound on the
Mordell-Weil rank of an elliptic curve over `ℚ`, `rank E(ℚ) ≥ ρ - t`. It is pure data; downstream
checkers audit each field. The intended witness is the general Weierstrass model
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over `ℤ`.

## Fields

* The curve is the integral Weierstrass model with coefficients `a₁ a₂ a₃ a₄ a₆ : ℤ`.
* `rho : ℕ` is the number of independent points exhibited, and `points` lists their affine
  coordinates `(x, y) : ℚ × ℚ`.
* `labels` lists the `rho` descent columns `(p, θ) : ℕ × ℤ`, a prime `p` and a root `θ` of the
  2-division data mod `p`; each names a descent character `λ_{p,θ}`.
* `matB` / `matM` encode the `rho × rho` character matrix `B` over `𝔽₂` and its claimed inverse
  `M`, in the `List Nat` bitmask layout of `ECCompute.F2Invert` (`matB` by rows, `matM` by
  columns), so `F2Invert.checkInv rho matB matM` applies verbatim.
* `t : ℕ` is the rational `2`-torsion dimension `dim_{𝔽₂} E(ℚ)[2]`, and `torsionPrime : ℕ`
  witnesses it: for `t = 0`, a prime at which the `2`-torsion cubic has no root. Scaling by
  `u = 4x`, this is the monic cubic `u³ + b₂u² + 8b₄u + 16b₆` used by `ECCompute.hasRootMod`.

## Layout conventions

The four lists `points`, `labels`, `matB`, and `matM` all have length `rho`; the auditing checkers
enforce this.
-/

namespace ECCompute

/-- A certificate for the Mordell-Weil rank bound `rank E(ℚ) ≥ ρ - t`, over the integral
Weierstrass model `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. See the module docstring for the
field-by-field description. -/
structure Certificate where
  /-- The `x y` coefficient of the Weierstrass model. -/
  a₁ : ℤ
  /-- The `x²` coefficient of the Weierstrass model. -/
  a₂ : ℤ
  /-- The `y` coefficient of the Weierstrass model. -/
  a₃ : ℤ
  /-- The `x` coefficient of the Weierstrass model. -/
  a₄ : ℤ
  /-- The constant coefficient of the Weierstrass model. -/
  a₆ : ℤ
  /-- The claimed number of independent points, `ρ`; the target bound is `rank ≥ ρ - t`. -/
  rho : ℕ
  /-- The `ρ` rational points, as affine coordinates `(x, y)`. -/
  points : List (ℚ × ℚ)
  /-- The `ρ` descent-column labels `(p, θ)`: a prime `p` and a root `θ` mod `p`. -/
  labels : List (ℕ × ℤ)
  /-- The `ρ × ρ` character matrix `B` over `𝔽₂`, as `List Nat` row bitmasks (see `F2Invert`). -/
  matB : List Nat
  /-- The claimed inverse `M` of `B` over `𝔽₂`, as `List Nat` column bitmasks (see `F2Invert`). -/
  matM : List Nat
  /-- The rational `2`-torsion dimension `t = dim_{𝔽₂} E(ℚ)[2]`; the target bound is
  `rank ≥ ρ - t`. -/
  t : ℕ
  /-- A prime witnessing the `2`-torsion claim (for `t = 0`, one at which the `2`-division cubic has
  no root). -/
  torsionPrime : ℕ
  deriving Repr, DecidableEq

end ECCompute
