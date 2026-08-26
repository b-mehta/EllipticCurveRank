/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Bitwise

/-!
## Evaluator-side helpers

These functions reproduce the descent character and the `𝔽₂` matrix inverse using plain
`Int`/`Nat` arithmetic, written for the compiler/interpreter. The `certify_curve` elaborator
calls them to produce a certificate's character matrix `B` and its inverse `M`.
-/

namespace ECCompute.CertifyEval

/-- The quadratic-residue bitmask mod an odd prime `p`: bit `a` set iff `a` is a nonzero square mod
`p`, computed as the OR of `1 <<< (j² % p)` for `j = 1 .. (p-1)/2`. Matches `ECCompute.qrMask`. -/
public def qrMaskNat (p : Nat) : Nat :=
  (List.range ((p - 1) / 2)).foldl (fun acc k ↦ acc ||| (1 <<< ((k + 1) * (k + 1) % p))) 0

/-- Evaluator-side value of the descent character `λ_{p,θ}` on a point whose `x`-coordinate is
`xnum / xden`, mirroring `ECCompute.lambdaK` (`true` = nontrivial). `a₂ a₄` are the short-model
coefficients and `qrMask` is `qrMaskNat p`. The character is nontrivial exactly when the relevant
value is a non-residue (or zero) mod `p`, i.e. its bit in `qrMask` is clear. -/
public def lambdaEval (a₂ a₄ : Int) (p : Nat) (qrMask : Nat) (θ xnum : Int) (xden : Nat) : Bool :=
  if (xden : Int) % (p : Int) == 0 then false
  else
    let α := (xnum - θ * (xden : Int)) % (p : Int)
    -- tangent case `x.num ≡ θ·x.den`: evaluate at the derivative `3θ² + 2a₂θ + a₄`
    let a := if α == 0 then 3 * θ ^ 2 + 2 * a₂ * θ + a₄ else α
    let am := (((a % (p : Int)) + p) % (p : Int)).toNat
    ((qrMask >>> am) &&& 1) == 0

/-- Pack booleans `p 0, …, p (n-1)` into a `Nat` bitmask: bit `j` set iff `p j`. -/
public def bitmaskOf (n : Nat) (p : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc j ↦ if p j then acc ||| (1 <<< j) else acc) 0

/-- The descent-character matrix `B` as `Nat` row bitmasks: row `i` has bit `j` set iff the
character of label `ls[j]` on the point with `x`-coordinate `xs[i] = (num, den)` is nontrivial. The
quadratic-residue bitmask of each label's prime is computed once. -/
public def computeB (a₂ a₄ : Int) (xs : List (Int × Nat)) (ls : List (Nat × Int)) : List Nat :=
  let qs := ls.map fun l ↦ qrMaskNat l.1
  xs.map fun x ↦
    bitmaskOf ls.length (fun j ↦ let l := ls[j]!; lambdaEval a₂ a₄ l.1 qs[j]! l.2 x.1 x.2)

/-- Invert an `n × n` matrix over `𝔽₂` given as `Nat` row bitmasks, returning the inverse in the
column-bitmask convention of `F2Invert.toMatCols` (so it feeds `checkInv` as `M`). Returns
`none` if the matrix is singular. -/
public def invF2 (B : Array Nat) (n : Nat) : Option (List Nat) := Id.run do
  let mut a := B
  let mut inv : Array Nat := (Array.range n).map (fun i ↦ (1 <<< i : Nat))
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
  return some <| (List.range n).map fun k ↦
    bitmaskOf n (fun j ↦ inv[j]!.testBit k)

end ECCompute.CertifyEval
