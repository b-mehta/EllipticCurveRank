/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Kernel-reducible definitions

The kernel-reducible `Bool` checkers and the `Nat`/`Int`/`List` arithmetic they fold over. The
correctness proofs and the abstract-typed spec definitions live in `ECCompute.Soundness.*`.

Currently the `Bool` folds `allBelow`/`allList`, the small-prime trial-division checkers, the monic
residue search, and the 𝔽₂ matrix-inverse checker.
-/

namespace ECCompute

/-- Kernel-reducible bounded `∀`: `true` iff `p m = true` for every `m < n`. -/
noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  n.rec true fun m r ↦ (p m).and' r

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r ↦ (p a).and' r

/-! ## Primes -/

/-- Trial division as a `Bool`-valued fold: `passes x L = true` iff no `i ∈ L` with `i < x`
divides `x`. -/
noncomputable def passes (x : Nat) : List Nat → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

/-- Kernel `Bool`: `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`ECCompute.passes`). -/
noncomputable def checkPrime (p : Nat) : Bool :=
  (Nat.ble 2 p).and' ((p.ble 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

/-- Kernel `Bool`: every label's prime component passes `checkPrime`. -/
noncomputable def checkPrimes (labels : List (Nat × Int)) : Bool :=
  allList (fun l ↦ checkPrime l.1) labels

/-! ## Monic residue search -/

/-- The monic integer polynomial with lower coefficients `cs` (constant term first) and leading
coefficient `1`, evaluated at `u`. -/
noncomputable def monicEval (cs : List Int) (u : Int) : Int :=
  cs.rec 1 fun c _ acc ↦ c.add (u.mul acc)

/-- `monicEval` at `r` reduced mod `ℓ` in `Nat`, each coefficient taken to its residue as the fold
reaches it. -/
noncomputable def monicModL (cs : List Int) (ℓ r : Nat) : Nat :=
  cs.rec 1 fun c _ acc ↦ ((c.emod ℓ).toNat.add (r.mul acc)).mod ℓ

/-- The integer polynomial with coefficients `cs` (constant term first, leading coefficient last),
evaluated at `u`. Unlike `monicEval`, the leading coefficient is explicit in `cs`. -/
noncomputable def polyEval (cs : List Int) (u : Int) : Int :=
  cs.rec 0 fun c _ acc ↦ c.add (u.mul acc)

/-- `polyEval` at `r` reduced mod `ℓ` in `Nat`, each coefficient taken to its residue as the Horner
fold reaches it. Unlike `monicModL`, the leading coefficient is explicit in `cs`. -/
noncomputable def polyModL (cs : List Int) (ℓ r : Nat) : Nat :=
  cs.rec 0 fun c _ acc ↦ ((c.emod ℓ).toNat.add (r.mul acc)).mod ℓ

/-- Kernel-reducible test: `true` iff the monic integer polynomial with coefficients `cs` has no
root modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1` in `Nat` (mod `ℓ`). -/
noncomputable def monicHasNoRootMod (cs : List Int) (ℓ : Nat) : Bool :=
  allBelow ℓ fun r ↦ ((monicModL cs ℓ r).beq 0).not'

/-! ## Descent label check -/

/-- `discrInt` written with the raw `Int.mul`/`Int.add`/`Int.sub`/`Int.neg` primitives, powers
expanded. -/
def discrIntK (a₂ a₄ a₆ : Int) : Int :=
  let b2 := Int.mul 4 a₂
  let b4 := Int.mul 2 a₄
  let b6 := Int.mul 4 a₆
  ((((b2.mul b2).mul (((Int.mul 4 a₂).mul a₆).sub (a₄.mul a₄))).neg.sub
      (Int.mul 8 ((b4.mul b4).mul b4))).sub (Int.mul 27 (b6.mul b6))).add
    (((Int.mul 9 b2).mul b4).mul b6)

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`, where `f(θ) = θ³ + a₂θ² + a₄θ + a₆` is read as the monic cubic
`monicModL [a₆, a₄, a₂]` evaluated at the residue of `θ`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : Int) (p : Nat) (θ : Int) : Bool :=
  (((Nat.mod 6 p).beq 0).not').and'
    (((((discrIntK (a₂.emod p) (a₄.emod p) (a₆.emod p)).emod p).beq' 0).not').and'
      ((monicModL [a₆, a₄, a₂] p (θ.emod p).toNat).beq 0))

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : Int) (labels : List (Nat × Int)) : Bool :=
  allList (fun l ↦ checkLabel a₂ a₄ a₆ l.1 l.2) labels

/-! ## Descent character -/

/-- Reference quadratic-residue-mask builder: OR together `1 <<< (j² % p)` for `j = 1 .. fuel`. With
`fuel = (p-1)/2` this sets exactly the bits at the nonzero quadratic residues mod an odd prime `p`,
using `Nat` primitives only. -/
noncomputable def qrMaskGo (p : Nat) : Nat → Nat :=
  Nat.rec 0 (fun k ih ↦ ih.lor (Nat.shiftLeft 1 ((k.succ.mul k.succ).mod p)))

/-- The quadratic-residue bitmask mod `p`: bit `a` is set iff `a` is a nonzero square mod `p`. -/
noncomputable def qrMask (p : Nat) : Nat := qrMaskGo p ((p.sub 1).div 2)

/-- Kernel-reducible character lookup: `true` iff bit `a` of the quadratic-residue mask `qmask` is
set, i.e. (for `qmask = qrMask p`, `a < p`, `p` odd prime) iff `a` is a nonzero square mod `p`. -/
noncomputable def qrLookupBool (qmask a : Nat) : Bool := ((qmask.shiftRight a).land 1).beq 1

/-- Residue in `[0, p)` of `x.num - θ·x.den`, from the `mp - mn` pair `(xp, xm)` for `x.num` and the
label residue `tval` for `θ`. -/
noncomputable def alphaResNat (p tval xp xm xden : Nat) : Nat :=
  ((xp.mod p).add (p.sub ((xm.add (tval.mul xden)).mod p))).mod p

/-- Residue in `[0, p)` of `f'(θ) = 3θ² + 2a₂θ + a₄`, from the `mp - mn` pairs `(c2p, c2m)` for `a₂`
and `(c4p, c4m)` for `a₄`, read as the polynomial `polyModL [a₄, 2a₂, 3]` at `tval`. -/
noncomputable def fderivResNat (c2p c2m c4p c4m p tval : Nat) : Nat :=
  polyModL [(c4p : Int) - c4m, 2 * ((c2p : Int) - c2m), 3] p tval

/-- Fully `Nat` mirror of `lambdaComputeBool`; signed inputs carried as `mp - mn`, the two character
evaluations bit tests against a supplied quadratic-residue mask `qmask`. -/
noncomputable def lambdaComputeBoolNatMask (c2p c2m c4p c4m p qmask tval xp xm xden : Nat) : Bool :=
  ((xden.mod p).beq 0).rec
    (((alphaResNat p tval xp xm xden).beq 0).rec
      ((qrLookupBool qmask (alphaResNat p tval xp xm xden)).not')
      ((qrLookupBool qmask (fderivResNat c2p c2m c4p c4m p tval)).not'))
    false

/-! ## 𝔽₂ matrix inverse -/

namespace F2Invert

/-- XOR of the low 32 bits of `v`, folded into bit 0 by five shift-xor stages (16, 8, 4, 2, 1).
For input `v < 2 ^ n` this equals the spec `popParity n v` (`popParityK_eq`), the range `checkInv`
enforces through `maskBelow`. -/
noncomputable def popParityK (v : Nat) : Bool :=
  let v := v.xor (v.shiftRight 16); let v := v.xor (v.shiftRight 8)
  let v := v.xor (v.shiftRight 4); let v := v.xor (v.shiftRight 2)
  let v := v.xor (v.shiftRight 1)
  (v.land 1).beq 1

/-- One row's contribution to the inverse check: for the row bitmask `bi` at row index `i`, fold
over the columns of `M`, comparing the parity of `bi &&& mₖ` (via `popParityK`) against the diagonal
indicator `i == k`. Soundness of the fold requires `bi, mₖ < 2 ^ n` with `n ≤ 32`, which `checkInv`
verifies separately. -/
noncomputable def checkInvRow (bi i k : Nat) (M : List Nat) : Bool :=
  M.rec (fun _ ↦ true)
    (fun m _ ih k ↦ ((popParityK (bi.land m)).rec (motive := fun _ ↦ Bool)
      (i.beq k).not' (i.beq k)).and' (ih k.succ)) k

/-- Fold over the rows of `B`, checking each against the columns of `M` with `checkInvRow`. -/
noncomputable def checkInvGo (M : List Nat) (i : Nat) (B : List Nat) : Bool :=
  B.rec (fun _ ↦ true)
    (fun b _ ih i ↦ (checkInvRow b i 0 M).and' (ih i.succ)) i

/-- Every mask in `M` fits in `n` bits (`< 2 ^ n`). -/
noncomputable def maskBelow (n : Nat) (M : List Nat) : Bool :=
  allList (fun x ↦ x.blt (Nat.shiftLeft 1 n)) M

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. Also verifies that all
masks fit in `n ≤ 32` bits, which `popParityK` relies on for soundness. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (maskBelow n B).and' ((maskBelow n M).and' ((n.ble 32).and' (checkInvGo M 0 B)))

end F2Invert

end ECCompute
