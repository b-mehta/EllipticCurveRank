/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Evaluator-side helpers for the `certify_curve` command

These functions reproduce the descent character and the `𝔽₂` matrix inverse using plain
`Int`/`Nat`/`Rat` arithmetic (the Legendre symbol via quadratic reciprocity), written for the
compiler/interpreter.
The `certify_curve` elaborator uses them to produce a certificate's character matrix `matB` and its
inverse `matM`.

This module imports nothing (`ℚ` is the core type `Rat`), so it stays cheap to build.
-/

namespace ECCompute.CertifyEval

/-- The Jacobi symbol `(a | n)` for odd `n`, by quadratic reciprocity.  For prime `n` this is
the Legendre symbol.  Returns `0`, `1`, or `-1`. -/
partial def jacobi (a : Int) (n : Nat) : Int := Id.run do
  let mut a := ((a % (n : Int)) + n).toNat % n
  let mut n := n
  let mut acc : Int := 1
  while a != 0 do
    while a % 2 == 0 do
      a := a / 2
      if n % 8 == 3 || n % 8 == 5 then acc := -acc
    let t := a; a := n; n := t
    if a % 4 == 3 && n % 4 == 3 then acc := -acc
    a := a % n
  return if n == 1 then acc else 0

/-- Evaluator-side value of the descent character `λ_{p,θ}` on a point whose `x`-coordinate is
`xnum / xden`, mirroring `ECCompute.lambdaComputeBool` (`true` = nontrivial).  `a₂ a₄` are the
short-model coefficients; the cubic's constant term `a₆` does not enter the character. -/
def lambdaEval (a₂ a₄ : Int) (p : Nat) (θ xnum : Int) (xden : Nat) : Bool :=
  if (xden : Int) % (p : Int) == 0 then false
  else
    let α := (xnum - θ * (xden : Int)) % (p : Int)
    -- tangent case `x.num ≡ θ·x.den`: evaluate at the derivative `3θ² + 2a₂θ + a₄`
    let a := if α == 0 then 3 * θ ^ 2 + 2 * a₂ * θ + a₄ else α
    jacobi a p != 1

/-- The descent-character matrix `matB` as `Nat` row bitmasks: row `i` has bit `j` set iff the
character of label `labs[j]` on the point with `x`-coordinate `xs[i] = (num, den)` is nontrivial. -/
def computeMatB (a₂ a₄ : Int) (xs : List (Int × Nat)) (labs : List (Nat × Int)) : List Nat :=
  xs.map fun x =>
    (List.range labs.length).foldl (fun acc j =>
      let lab := labs[j]!
      if lambdaEval a₂ a₄ lab.1 lab.2 x.1 x.2 then acc ||| (1 <<< j) else acc) 0

/-- Invert an `n × n` matrix over `𝔽₂` given as `Nat` row bitmasks, returning the inverse in the
column-bitmask convention of `F2Invert.toMatCols` (so it feeds `checkInv` as `matM`).  Returns
`none` if the matrix is singular. -/
def invF2 (B : Array Nat) (n : Nat) : Option (List Nat) := Id.run do
  let mut a := B
  let mut inv : Array Nat := (Array.range n).map (fun i => (1 <<< i : Nat))
  for col in [0:n] do
    let mut piv : Option Nat := none
    for r in [col:n] do
      if a[r]!.testBit col then
        piv := some r
        break
    match piv with
    | none => return none
    | some r =>
      if r != col then
        let ta := a[col]!; a := a.set! col a[r]!; a := a.set! r ta
        let ti := inv[col]!; inv := inv.set! col inv[r]!; inv := inv.set! r ti
      for r2 in [0:n] do
        if r2 != col && a[r2]!.testBit col then
          a := a.set! r2 (a[r2]! ^^^ a[col]!)
          inv := inv.set! r2 (inv[r2]! ^^^ inv[col]!)
  return some <| (List.range n).map fun k =>
    (List.range n).foldl (fun acc j => if inv[j]!.testBit k then acc ||| (1 <<< j) else acc) 0

end ECCompute.CertifyEval
