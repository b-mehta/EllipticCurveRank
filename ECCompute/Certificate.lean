/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Rat.Defs

/-!
# The rank-bound certificate data type

`Certificate` bundles the data a referee audits to accept a lower bound on the Mordell-Weil rank
of an elliptic curve over `ℚ`, `rank E(ℚ) ≥ ρ - t`. Its curve is the short integral Weierstrass
model `y² = x³ + a₂x² + a₄x + a₆`; `ECCompute.hasRankGE_of_certificate` transports the bound to a
general integral model.

## Main definitions

* `ECCompute.Certificate`: the certificate record; see its field docstrings for each entry.

## Implementation notes

The five lists `points`, `labels`, `matB`, `matM` and `qrMasks` all have length `rho`; the auditing
checkers enforce this. `matB` / `matM` follow the `List Nat` bitmask layout of `ECCompute.F2Invert`
(`matB` by rows, `matM` by columns), so `F2Invert.checkInv rho matB matM` applies verbatim.
-/

namespace ECCompute

/-- A certificate for the Mordell-Weil rank bound `rank E(ℚ) ≥ ρ - t`, over the short integral
Weierstrass model `y² = x³ + a₂x² + a₄x + a₆`. -/
structure Certificate where
  /-- The `x²` coefficient of the short model. -/
  a₂ : ℤ
  /-- The `x` coefficient of the short model. -/
  a₄ : ℤ
  /-- The constant coefficient of the short model. -/
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
  /-- The `ρ` quadratic-residue masks, one per label: `qrMasks[j]` is the bitmask whose bit `a` is
  set iff `a` is a nonzero square mod `labels[j].1`. Checked against `qrMask` by the referee, so
  each Legendre-character check is a bitmask lookup. -/
  qrMasks : List Nat
  /-- The certified bound on the rational `2`-torsion, `|E(ℚ)[2]| ≤ 2 ^ t`; the target bound is
  `rank ≥ ρ - t`. -/
  t : ℕ
  /-- The prime witnessing the `2`-torsion bound: for `t = 0`, one at which the `2`-division cubic
  has no root; for `t = 1`, one at which the quadratic cofactor has no root. Ignored for `t = 2`,
  where the bound `|E(ℚ)[2]| ≤ 4` holds for every curve. -/
  torsionPrime : ℕ

end ECCompute
