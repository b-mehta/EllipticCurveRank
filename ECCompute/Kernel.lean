/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Kernel-reducible definitions

The kernel-reducible `Bool` checkers and the `Nat`/`Int`/`List` arithmetic they fold over. The
correctness proofs and the abstract-typed spec definitions live in `ECCompute.Soundness.*`.

Currently the `Bool` folds `allBelow`/`allList`, the small-prime trial-division checkers, the monic
residue search, the descent label and character checks, the 𝔽₂ matrix-inverse checker, the
aggregate descent-matrix check, and the point-on-curve check.
-/

@[expose] public section

namespace ECCompute

/-- `true` iff `p m = true` for every `m < n`. -/
noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool := n.rec true fun m r ↦ (p m).and' r

/-- `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r ↦ (p a).and' r

/-! ## Primes -/

/-- `true` iff no `i ∈ L` with `i < x` divides `x`. -/
noncomputable def passes (x : Nat) : List Nat → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

/-- `true` iff `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`ECCompute.passes`). -/
noncomputable def checkPrime (p : Nat) : Bool :=
  (Nat.ble 2 p).and' ((p.ble 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

/-- `true` iff every label's prime component passes `checkPrime`. -/
noncomputable def checkPrimes (labels : List (Nat × Int)) : Bool :=
  allList (fun l ↦ checkPrime l.1) labels

/-! ## Polynomial residue search -/

/-- The integer polynomial with coefficients `cs` (constant term first, leading coefficient last),
evaluated at `u`. -/
noncomputable def polyEval (cs : List Int) (u : Int) : Int :=
  cs.rec 0 fun c _ acc ↦ c.add (u.mul acc)

/-- `polyEval` at `r` reduced mod `ℓ` in `Nat`, each coefficient taken to its residue as the Horner
fold reaches it. -/
noncomputable def polyModL (cs : List Int) (ℓ r : Nat) : Nat :=
  cs.rec 0 fun c _ acc ↦ ((c.emod ℓ).toNat.add (r.mul acc)).mod ℓ

/-- `true` iff the monic integer polynomial with lower coefficients `cs`
(implicit leading coefficient `1`) has no root modulo `ℓ`, trying every residue `0, …, ℓ - 1`. -/
noncomputable def monicHasNoRootMod (cs : List Int) (ℓ : Nat) : Bool :=
  allBelow ℓ fun r ↦ ((polyModL (cs ++ [1]) ℓ r).beq 0).not'

/-! ## Descent label check -/

/-- The discriminant of the integral model `curve a₂ a₄ a₆`, for the kernel. -/
def discrIntK (a₂ a₄ a₆ : Int) : Int :=
  let b2 := Int.mul 4 a₂
  let b4 := Int.mul 2 a₄
  let b6 := Int.mul 4 a₆
  ((((b2.mul b2).mul (((Int.mul 4 a₂).mul a₆).sub (a₄.mul a₄))).neg.sub
      (Int.mul 8 ((b4.mul b4).mul b4))).sub (Int.mul 27 (b6.mul b6))).add
    (((Int.mul 9 b2).mul b4).mul b6)

/-- `true` iff the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`, where `f(θ) = θ³ + a₂θ² + a₄θ + a₆` is read as the monic cubic
`polyModL [a₆, a₄, a₂, 1]` evaluated at the residue of `θ`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : Int) (p : Nat) (θ : Int) : Bool :=
  (((Nat.mod 6 p).beq 0).not').and'
    (((((discrIntK (a₂.emod p) (a₄.emod p) (a₆.emod p)).emod p).beq' 0).not').and'
      ((polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0))

/-- `true` iff every label passes `checkLabel`. -/
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

/-- `true` iff bit `a` of the quadratic-residue mask `qmask` is
set, i.e. (for `qmask = qrMask p`, `a < p`, `p` odd prime) iff `a` is a nonzero square mod `p`. -/
noncomputable def qrLookupBool (qmask a : Nat) : Bool := ((qmask.shiftRight a).land 1).beq 1

/-- Residue in `[0, p)` of `x.num - θ·x.den`, for the kernel. -/
noncomputable def alphaResK (p tval xp xm xden : Nat) : Nat :=
  ((xp.mod p).add (p.sub ((xm.add (tval.mul xden)).mod p))).mod p

/-- Residue in `[0, p)` of `f'(θ) = 3θ² + 2a₂θ + a₄`, for the kernel. -/
noncomputable def fderivResK (a₂ a₄ : Int) (p tval : Nat) : Nat :=
  polyModL [a₄, Int.mul 2 a₂, 3] p tval

/-- The value of the descent character `λ_{p,θ}` at a point. -/
noncomputable def lambdaK (a₂ a₄ : Int) (p qmask tval xp xm xden : Nat) : Bool :=
  ((xden.mod p).beq 0).rec
    (((alphaResK p tval xp xm xden).beq 0).rec
      ((qrLookupBool qmask (alphaResK p tval xp xm xden)).not')
      ((qrLookupBool qmask (fderivResK a₂ a₄ p tval)).not'))
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

/-- `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. Also verifies that all
masks fit in `n ≤ 32` bits, which `popParityK` relies on for soundness. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (maskBelow n B).and' ((maskBelow n M).and' ((n.ble 32).and' (checkInvGo M 0 B)))

end F2Invert

/-! ## Descent matrix -/

/-- The `Nat` label triples `(p, (θ % p).toNat, m)`, one for each label `(p, θ)` in `ls` paired
with its quadratic-residue mask `m` in `q`. -/
noncomputable def toLs (ls : List (Nat × Int)) (q : List Nat) : List (Nat × Nat × Nat) :=
  List.zipWith (fun l m ↦ (l.1, (l.2.emod l.1).toNat, m)) ls q

/-- `true` iff bit `j` of `b` matches label `ls[j]`'s descent character at point
`(xnp - xnm) / xden`, for every `j`, evaluated with the integer coefficients `a₂ a₄`. -/
noncomputable def checkBRow (a₂ a₄ : Int) (xnp xnm xden b : Nat) (ls : List (Nat × Nat × Nat)) :
    Bool :=
  ls.rec (fun _ ↦ true)
    (fun l _ ih b ↦
      (((b.mod 2).beq 1).rec (motive := fun _ ↦ Bool)
        (lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (ih (b.div 2))) b

/-- `true` iff every row of `B` passes `checkBRow` against its point at the same index in `pt`. -/
noncomputable def checkBGo (a₂ a₄ : Int) (ls : List (Nat × Nat × Nat)) (B : List Nat)
    (pt : List (Rat × Rat)) : Bool :=
  B.rec (fun _ ↦ true)
    (fun b _ ih pt ↦ pt.rec true
      (fun p ps _ ↦ (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b ls).and'
        (ih ps))) pt

/-- `true` iff each triple's mask equals `qrMask p` for its prime `p`. -/
noncomputable def checkMaskList (ls : List (Nat × Nat × Nat)) : Bool :=
  allList (fun l ↦ (qrMask l.1).beq l.2.2) ls

/-- `true` iff every entry of `B` equals the descent character at its point in `pt`, with each
mask in `q` checked against `qrMask`. Spec: `checkB_true`. -/
noncomputable def checkB (a₂ a₄ : Int) (ls : List (Nat × Int)) (q B : List Nat)
    (pt : List (Rat × Rat)) : Bool :=
  (checkMaskList (toLs ls q)).and'
    (checkBGo a₂ a₄ (toLs ls q) B pt)

/-! ## Point on curve -/

/-- `true` iff `(x, y)` lies on the curve. Writing `x = xn/xd` and `y = yn/yd` in lowest terms, the
Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` is equivalent, after clearing the
denominator `xd³·yd²`, to an identity between integers, which `checkPoint` tests. -/
noncomputable def checkPoint (a₁ a₂ a₃ a₄ a₆ : Int) (x y : Rat) : Bool :=
  let xn := x.num; let xd := x.den
  let yn := y.num; let yd := y.den
  let xd2 := xd.mul xd; let xd3 := xd2.mul xd
  let yd2 := yd.mul yd
  let xn2 := xn.mul xn; let xn3 := xn2.mul xn
  let yn2 := yn.mul yn
  (((yn2.mul xd3).add ((((a₁.mul xn).mul yn).mul xd2).mul yd)).add
      (((a₃.mul yn).mul xd3).mul yd)).beq'
    ((((xn3.mul yd2).add (((a₂.mul xn2).mul xd).mul yd2)).add
        (((a₄.mul xn).mul xd2).mul yd2)).add ((a₆.mul xd3).mul yd2))

/-- `true` iff every point in `pts` lies on the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : Int) (pts : List (Rat × Rat)) : Bool :=
  allList (fun p ↦ checkPoint a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

/-- `checkPointShort a₂ a₄ a₆ x y` tests the cleared short-model Weierstrass identity
`yn²·xd³ = xn³·yd² + a₂·xn²·xd·yd² + a₄·xn·xd²·yd² + a₆·xd³·yd²` at `x = xn/xd`, `y = yn/yd`.
Spec: `checkPointShort_iff`. -/
noncomputable def checkPointShort (a₂ a₄ a₆ : Int) (x y : Rat) : Bool :=
  let xn := x.num; let xd := x.den
  let yn := y.num; let yd := y.den
  let xd2 := xd.mul xd; let xd3 := xd2.mul xd
  let yd2 := yd.mul yd
  let xn2 := xn.mul xn; let xn3 := xn2.mul xn
  let yn2 := yn.mul yn
  (yn2.mul xd3).beq'
    ((((xn3.mul yd2).add (((a₂.mul xn2).mul xd).mul yd2)).add
        (((a₄.mul xn).mul xd2).mul yd2)).add ((a₆.mul xd3).mul yd2))

/-- `true` iff every point in `pts` lies on the short model `⟨0, a₂, 0, a₄, a₆⟩`. -/
noncomputable def checkPointsShort (a₂ a₄ a₆ : Int) (pts : List (Rat × Rat)) : Bool :=
  allList (fun p ↦ checkPointShort a₂ a₄ a₆ p.1 p.2) pts

end ECCompute
