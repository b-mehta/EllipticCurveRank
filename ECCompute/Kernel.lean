/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Rat.Defs

/-!
# Kernel-reducible definitions

Every kernel-reducible `Bool` checker and the `Nat`/`Int`/`ℚ`/`List` arithmetic it folds over. Every
declaration stays within those concrete types; the abstract-typed spec definitions (`ZMod`,
`Matrix`, the `ℤ`-ring `^`) and all correctness proofs live in `ECCompute.Soundness.*`.
-/

namespace ECCompute

/-! ## Bounded and list folds -/

/-- Kernel-reducible bounded `∀`: `true` iff `p m = true` for every `m < n`. -/
noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  n.rec true fun m r ↦ (p m).and' r

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r ↦ (p a).and' r

/-! ## Point on curve -/

/-- Kernel-reducible point-on-curve check. Writing `x = xn/xd` and `y = yn/yd` in lowest terms, the
Weierstrass equation is equivalent, after clearing the denominator `xd³·yd²`, to an identity between
integers, which `checkPoint` tests. -/
noncomputable def checkPoint (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) : Bool :=
  let xn := x.num; let xd := (x.den : ℤ)
  let yn := y.num; let yd := (y.den : ℤ)
  let xd2 := xd.mul xd; let xd3 := xd2.mul xd
  let yd2 := yd.mul yd
  let xn2 := xn.mul xn; let xn3 := xn2.mul xn
  let yn2 := yn.mul yn
  (((yn2.mul xd3).add ((((a₁.mul xn).mul yn).mul xd2).mul yd)).add
      (((a₃.mul yn).mul xd3).mul yd)).beq'
    ((((xn3.mul yd2).add (((a₂.mul xn2).mul xd).mul yd2)).add
        (((a₄.mul xn).mul xd2).mul yd2)).add ((a₆.mul xd3).mul yd2))

/-- Check that every point in a list lies on the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  allList (fun p ↦ checkPoint a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

/-! ## Primes -/

/-- Trial division as a `Bool`-valued fold: `passes x L = true` iff no `i ∈ L` with `i < x`
divides `x`. -/
noncomputable def passes (x : ℕ) : List ℕ → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

/-- Kernel `Bool`: `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`ECCompute.passes`). -/
noncomputable def checkPrime (p : ℕ) : Bool :=
  (Nat.ble 2 p).and' ((p.ble 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

/-- Kernel `Bool`: every label's prime component passes `checkPrime`. -/
noncomputable def checkPrimes (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l ↦ checkPrime l.1) labels

/-! ## Roots modulo a prime

A coefficient list `cs` gives the lower coefficients constant term first; the leading coefficient
`1` is implicit, so `[c₀, c₁, c₂]` is `u³ + c₂u² + c₁u + c₀` and `[c₀, c₁]` is `u² + c₁u + c₀`. -/

/-- The monic integer polynomial with lower coefficients `cs` (constant term first) and leading
coefficient `1`, evaluated at `u`. -/
noncomputable def monicEval (cs : List ℤ) (u : ℤ) : ℤ :=
  cs.rec 1 fun c _ acc ↦ c.add (u.mul acc)

/-- `monicEval` at `r` reduced mod `ℓ` in `Nat`, each coefficient taken to its residue as the fold
reaches it. -/
noncomputable def monicModL (cs : List ℤ) (ℓ r : ℕ) : ℕ :=
  cs.rec 1 fun c _ acc ↦ ((c.emod ℓ).toNat.add (r.mul acc)).mod ℓ

/-- Kernel-reducible test: `true` iff the monic integer polynomial with coefficients `cs` has no
root modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1` in `Nat` (mod `ℓ`). -/
noncomputable def monicHasNoRootMod (cs : List ℤ) (ℓ : ℕ) : Bool :=
  allBelow ℓ fun r ↦ ((monicModL cs ℓ r).beq 0).not'

/-! ## Descent character (λ) -/

/-- Reference quadratic-residue-mask builder: OR together `1 <<< (j² % p)` for `j = 1 .. fuel`. With
`fuel = (p-1)/2` this sets exactly the bits at the nonzero quadratic residues mod an odd prime `p`,
using `Nat` primitives only. -/
noncomputable def qrMaskGo : Nat → Nat → Nat :=
  Nat.rec (fun _ ↦ 0)
    (fun k ih p ↦ (ih p).lor (Nat.shiftLeft 1 ((k.succ.mul k.succ).mod p)))

/-- The quadratic-residue bitmask mod `p`: bit `a` is set iff `a` is a nonzero square mod `p`. -/
noncomputable def qrMask (p : Nat) : Nat := qrMaskGo ((p.sub 1).div 2) p

/-- Kernel-reducible character lookup: `true` iff bit `a` of the quadratic-residue mask `qmask` is
set, i.e. (for `qmask = qrMask p`, `a < p`, `p` odd prime) iff `a` is a nonzero square mod `p`. -/
noncomputable def qrLookupBool (qmask a : ℕ) : Bool := ((qmask.shiftRight a).land 1).beq 1

/-- Residue in `[0, p)` of `x.num - θ·x.den`, from the `mp - mn` pair `(xp, xm)` for `x.num` and the
label residue `tval` for `θ`. -/
noncomputable def alphaResNat (p tval xp xm xden : ℕ) : ℕ :=
  ((xp.mod p).add (p.sub ((xm.add (tval.mul xden)).mod p))).mod p

/-- Residue in `[0, p)` of `f'(θ) = 3θ² + 2a₂θ + a₄`, from the `mp - mn` pairs `(c2p, c2m)` for `a₂`
and `(c4p, c4m)` for `a₄`. -/
noncomputable def fderivResNat (c2p c2m c4p c4m p tval : ℕ) : ℕ :=
  ((((((Nat.mul 3 tval).mul tval).add ((Nat.mul 2 c2p).mul tval)).add c4p).mod p).add
    (p.sub ((((Nat.mul 2 c2m).mul tval).add c4m).mod p))).mod p

/-- Fully `Nat` mirror of `lambdaComputeBool`; signed inputs carried as `mp - mn`, the two character
evaluations bit tests against a supplied quadratic-residue mask `qmask`. For `qmask = qrMask p`
(`p` an odd prime) it agrees with `lambdaComputeBool` (see `lambdaComputeBoolNatMask_eq`). -/
noncomputable def lambdaComputeBoolNatMask (c2p c2m c4p c4m p qmask tval xp xm xden : ℕ) : Bool :=
  ((xden.mod p).beq 0).rec
    (((alphaResNat p tval xp xm xden).beq 0).rec
      ((qrLookupBool qmask (alphaResNat p tval xp xm xden)).not')
      ((qrLookupBool qmask (fderivResNat c2p c2m c4p c4m p tval)).not'))
    false

/-! ## Descent labels -/

/-- The label polynomial `f(θ) = θ³ + a₂θ² + a₄θ + a₆` reduced mod `p` in `Nat` (θ and the
coefficients reduced to residues first). -/
noncomputable def fvalModP (a₂ a₄ a₆ θ : ℤ) (p : ℕ) : ℕ :=
  ((((((θ.emod p).toNat.mul (θ.emod p).toNat).mul (θ.emod p).toNat).add
    ((a₂.emod p).toNat.mul ((θ.emod p).toNat.mul (θ.emod p).toNat))).add
    ((a₄.emod p).toNat.mul (θ.emod p).toNat)).add (a₆.emod p).toNat).mod p

/-- `discrInt` written with the raw `Int.mul`/`Int.add`/`Int.sub`/`Int.neg` primitives, powers
expanded. -/
noncomputable def discrIntK (a₂ a₄ a₆ : ℤ) : ℤ :=
  let b2 := Int.mul 4 a₂
  let b4 := Int.mul 2 a₄
  let b6 := Int.mul 4 a₆
  ((((b2.mul b2).mul (((Int.mul 4 a₂).mul a₆).sub (a₄.mul a₄))).neg.sub
      (Int.mul 8 ((b4.mul b4).mul b4))).sub
      (Int.mul 27 (b6.mul b6))).add
    (((Int.mul 9 b2).mul b4).mul b6)

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ) : Bool :=
  (((Nat.mod 6 p).beq 0).not').and'
    (((((discrIntK (a₂.emod p) (a₄.emod p) (a₆.emod p)).emod p).beq' 0).not').and'
      ((fvalModP a₂ a₄ a₆ θ p).beq 0))

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l ↦ checkLabel a₂ a₄ a₆ l.1 l.2) labels

/-! ## Descent-character matrix -/

/-- Turn the `(prime, θ)` labels and their quadratic-residue masks into the `Nat` label triples
`(p, (θ % p).toNat, q)` consumed by the kernel-reduced checker. -/
noncomputable def toLabN (lab : List (ℕ × ℤ)) (qms : List ℕ) : List (ℕ × ℕ × ℕ) :=
  List.zipWith (fun l q ↦ (l.1, (l.2.emod (l.1 : ℤ)).toNat, q)) lab qms

/-- One row of the descent-matrix check: for the row bitmask `b`, the point's `Nat` pieces and the
coefficient pairs, fold over the `Nat` label triples `labN = (p, tval, q)`, consuming `b` one bit at
a time, comparing each against the mask-based `Nat`-valued descent character. -/
noncomputable def checkBRow (c2p c2m c4p c4m xnp xnm xden b : ℕ) (labN : List (ℕ × ℕ × ℕ)) : Bool :=
  labN.rec (motive := fun _ ↦ ℕ → Bool) (fun _ ↦ true)
    (fun l _ ih b ↦
      (((b.mod 2).beq 1).rec (motive := fun _ ↦ Bool)
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (ih (b.div 2))) b

/-- Fold over the rows, pairing each row bitmask of `matB` with its point in `pt`, and check each
row with `checkBRow`. The point's numerator is split into `x.num.toNat - (-x.num).toNat`. -/
noncomputable def checkBGo (c2p c2m c4p c4m : ℕ) (labN : List (ℕ × ℕ × ℕ)) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  matB.rec (motive := fun _ ↦ List (ℚ × ℚ) → Bool) (fun _ ↦ true)
    (fun b _ ih pt ↦ pt.rec (motive := fun _ ↦ Bool) true
      (fun p ps _ ↦ (checkBRow c2p c2m c4p c4m p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (ih ps))) pt

/-- Verify every supplied mask: for each label triple `(p, _, q)`, `q` must equal `qrMask p`. -/
noncomputable def checkMaskList (labN : List (ℕ × ℕ × ℕ)) : Bool :=
  allList (fun l ↦ (qrMask l.1).beq l.2.2) labN

/-- The aggregate descent-matrix check. The coefficients become `mp - mn` pairs and the labels their
`Nat` residues and masks once, up front; the masks are verified by `checkMaskList` and then
`checkBGo` folds the rows entirely in `Nat`. -/
noncomputable def checkB (a₂ a₄ : ℤ) (lab : List (ℕ × ℤ)) (qms : List ℕ) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  (checkMaskList (toLabN lab qms)).and'
    (checkBGo a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat (toLabN lab qms) matB pt)

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
  M.rec (motive := fun _ ↦ Nat → Bool) (fun _ ↦ true)
    (fun m _ ih k ↦ ((popParityK (bi.land m)).rec (motive := fun _ ↦ Bool)
      (i.beq k).not' (i.beq k)).and' (ih k.succ)) k

/-- Fold over the rows of `B`, checking each against the columns of `M` with `checkInvRow`. -/
noncomputable def checkInvGo (M : List Nat) (i : Nat) (B : List Nat) : Bool :=
  B.rec (motive := fun _ ↦ Nat → Bool) (fun _ ↦ true)
    (fun b _ ih i ↦ (checkInvRow b i 0 M).and' (ih i.succ)) i

/-- Every mask in `L` fits in `n` bits (`< 2 ^ n`). -/
noncomputable def maskBelow (n : Nat) (L : List Nat) : Bool :=
  allList (fun x ↦ x.blt (Nat.shiftLeft 1 n)) L

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. Also verifies that all
masks fit in `n ≤ 32` bits, which `popParityK` relies on for soundness. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (maskBelow n B).and' ((maskBelow n M).and' ((n.ble 32).and' (checkInvGo M 0 B)))

end F2Invert

end ECCompute
