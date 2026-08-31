/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Rat.Defs
public import ECCompute.Soundness.F2Invert
public import ECCompute.Theory.Descent.Character

/-!
# The rank-bound certificate data type

`Certificate` bundles the data establishing a lower bound on the Mordell-Weil rank
of an elliptic curve over `ℚ`, `rank E(ℚ) ≥ ρ - t`. Its curve is the short integral Weierstrass
model `y² = x³ + a₂x² + a₄x + a₆`; `ECCompute.hasRankGE_of_certificate` transports the bound to a
general integral model.

## Main definitions

* `ECCompute.Certificate`: the certificate record; see its field docstrings for each entry.
* `ECCompute.Certificate.Valid`: the checks a certificate must pass on its own data.

## Implementation notes

The four lists `points`, `labels`, `B`, and `M` all have length `ρ`; the `Certificate.Valid`
checks enforce this. `B` / `M` follow the `List Nat` bitmask layout of `ECCompute.F2Invert` (`B`
and `M` both by rows), so `F2Invert.checkInv ρ B M` applies verbatim.
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
  /-- The product of every label's prime; each label prime divides it (checked in `checkLabels`). -/
  P : ℕ
  /-- The residue `(a₂ mod P)`, as a `Nat` literal; verified in `checkLabels`. -/
  a2r : ℕ
  /-- The residue `(a₄ mod P)`, as a `Nat` literal; verified in `checkLabels`. -/
  a4r : ℕ
  /-- The residue `(a₆ mod P)`, as a `Nat` literal; verified in `checkLabels`. -/
  a6r : ℕ
  /-- The discriminant residue `(Δ mod P)`, as a `Nat` literal; verified once in `checkLabels`
  against `discrModP a2r a4r a6r P`, so each label's `p ∤ Δ` test is a single `dr mod p`. -/
  dr : ℕ
  /-- The claimed number of independent points, `ρ`; the target bound is `rank ≥ ρ - t`. -/
  ρ : ℕ
  /-- The `ρ` rational points, as affine coordinates `(x, y)`. -/
  points : List (ℚ × ℚ)
  /-- The `ρ` descent-column labels as precomputed `Nat` triples `(p, tval, qrmask)`: a prime `p`,
  the root residue `tval = (θ mod p).toNat` of the `2`-division cubic mod `p`, and the
  quadratic-residue bitmask `qrmask` whose bit `a` is set iff `a` is a nonzero square mod `p`.
  `Certificate.Valid` checks `tval < p`, that `θ` is a root, and each mask against `qrMask`. -/
  labels : List (ℕ × ℕ × ℕ)
  /-- The `ρ × ρ` character matrix `B` over `𝔽₂`, as `List Nat` row bitmasks (see `F2Invert`). -/
  B : List Nat
  /-- The claimed inverse `M` of `B` over `𝔽₂`, as `List Nat` column bitmasks (see `F2Invert`). -/
  M : List Nat
  /-- The rational `2`-torsion dimension `t = dim_{𝔽₂} E(ℚ)[2]`; the target bound is
  `rank ≥ ρ - t`. -/
  t : ℕ
  /-- A prime witnessing the `2`-torsion claim (for `t = 0`, one at which the `2`-division cubic has
  no root). -/
  torsionPrime : ℕ

/-- The checks a certificate must pass on its own data: the five lists have length
`ρ`, the point, prime, label, and character-matrix checks pass, the claimed `𝔽₂` inverse is
correct, and the `2`-torsion order is at most `2 ^ t`. `hasRankGE_of_certificate` turns this,
together with a curve match, into a rank lower bound. -/
public structure Certificate.Valid (c : Certificate) : Prop where
  /-- The point list has `ρ` entries. -/
  lenP : c.points.length = c.ρ
  /-- The label list has `ρ` entries. -/
  lenL : c.labels.length = c.ρ
  /-- The row bitmask list `B` has `ρ` entries. -/
  lenB : c.B.length = c.ρ
  /-- The column bitmask list `M` has `ρ` entries. -/
  lenM : c.M.length = c.ρ
  /-- Each listed point lies on the short model. -/
  pts : checkPointsShort c.a₂ c.a₄ c.a₆ c.points
  /-- Each label carries a prime. -/
  primes : checkPrimes c.labels
  /-- Each label's `θ` is a root of the `2`-division cubic mod its prime. -/
  labels : checkLabels c.a₂ c.a₄ c.a₆ c.P c.a2r c.a4r c.a6r c.dr c.labels
  /-- `B` is the descent-character matrix the labels induce on the points. -/
  matrix : checkB c.a₂ c.a₄ c.labels c.B c.points
  /-- `M` inverts `B` over `𝔽₂`. -/
  inv : F2Invert.checkInv c.ρ c.B c.M
  /-- The rational `2`-torsion has order at most `2 ^ t`. -/
  tors : (curveQ c.a₂ c.a₄ c.a₆).twoTorsionPoints.ncard ≤ 2 ^ c.t

end ECCompute
