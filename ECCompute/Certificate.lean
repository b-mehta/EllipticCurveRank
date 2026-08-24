/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Rat.Defs
public import ECCompute.Soundness.F2Invert
public import ECCompute.Theory.Descent.Defs

/-!
# The rank-bound certificate data type

`Certificate` bundles the data a referee audits to accept a lower bound on the Mordell-Weil rank
of an elliptic curve over `ℚ`, `rank E(ℚ) ≥ ρ - t`. Its curve is the short integral Weierstrass
model `y² = x³ + a₂x² + a₄x + a₆`; `ECCompute.hasRankGE_of_certificate` transports the bound to a
general integral model.

## Main definitions

* `ECCompute.Certificate`: the certificate record; see its field docstrings for each entry.
* `ECCompute.Certificate.Valid`: the referee obligations a certificate carries on its own data.

## Implementation notes

The four lists `points`, `labels`, `B`, and `M` all have length `rho`; the auditing checkers
enforce this. `B` / `M` follow the `List Nat` bitmask layout of `ECCompute.F2Invert` (`B`
by rows, `M` by columns), so `F2Invert.checkInv rho B M` applies verbatim.
-/

namespace ECCompute

/-- A certificate for the Mordell-Weil rank bound `rank E(ℚ) ≥ ρ - t`, over the short integral
Weierstrass model `y² = x³ + a₂x² + a₄x + a₆`. -/
public structure Certificate where
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
  B : List Nat
  /-- The claimed inverse `M` of `B` over `𝔽₂`, as `List Nat` column bitmasks (see `F2Invert`). -/
  M : List Nat
  /-- The `ρ` quadratic-residue masks, one per label: `qrMasks[j]` is the bitmask whose bit `a` is
  set iff `a` is a nonzero square mod `labels[j].1`. Checked against `qrMask` by the referee, so
  each Legendre-character check is a bitmask lookup. -/
  qrMasks : List Nat
  /-- The rational `2`-torsion dimension `t = dim_{𝔽₂} E(ℚ)[2]`; the target bound is
  `rank ≥ ρ - t`. -/
  t : ℕ
  /-- A prime witnessing the `2`-torsion claim (for `t = 0`, one at which the `2`-division cubic has
  no root). -/
  torsionPrime : ℕ
  deriving Repr, DecidableEq

/-- The referee obligations a certificate carries on its own data: the five lists have length
`rho`, the point, prime, label, and character-matrix checks pass, the claimed `𝔽₂` inverse is
correct, and the `2`-torsion order is at most `2 ^ t`. `hasRankGE_of_certificate` turns this,
together with a curve match, into a rank lower bound. -/
public structure Certificate.Valid (c : Certificate) : Prop where
  /-- The point list has `rho` entries. -/
  lenP : c.points.length = c.rho
  /-- The label list has `rho` entries. -/
  lenL : c.labels.length = c.rho
  /-- The row bitmask list `B` has `rho` entries. -/
  lenB : c.B.length = c.rho
  /-- The column bitmask list `M` has `rho` entries. -/
  lenM : c.M.length = c.rho
  /-- The quadratic-residue mask list has `rho` entries. -/
  lenQ : c.qrMasks.length = c.rho
  /-- Each listed point lies on the short model. -/
  pts : checkPoints 0 c.a₂ 0 c.a₄ c.a₆ c.points
  /-- Each label carries a prime. -/
  primes : checkPrimes c.labels
  /-- Each label's `θ` is a root of the `2`-division cubic mod its prime. -/
  labels : checkLabels c.a₂ c.a₄ c.a₆ c.labels
  /-- `B` is the descent-character matrix the labels induce on the points. -/
  matrix : checkB c.a₂ c.a₄ c.labels c.qrMasks c.B c.points
  /-- `M` inverts `B` over `𝔽₂`. -/
  inv : F2Invert.checkInv c.rho c.B c.M
  /-- The rational `2`-torsion has order at most `2 ^ t`. -/
  tors : Nat.card {P : (curve c.a₂ c.a₄ c.a₆).toAffine.Point // P + P = 0} ≤ 2 ^ c.t

end ECCompute
