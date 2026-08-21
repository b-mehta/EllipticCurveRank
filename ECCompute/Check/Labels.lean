/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Check.Fold
import ECCompute.Check.IntResNat

/-!
# Column-legitimacy checks

For a descent label `(p, θ)` the referee verifies, by exact integer arithmetic, the hypotheses of
the descent lemma `ECCompute.DescentHyp`: `p ∤ 6`, `p ∤ Δ` (the integer discriminant of
`y² = x³ + a₂x² + a₄x + a₆`), and `f(θ) ≡ 0 (mod p)`. `checkLabel` decides all three by `Int`/`Nat`
`%` and `beq`, so a concrete instance closes by `rfl`; `checkLabels` lifts it to a list.

## Main declarations

* `ECCompute.discrInt`: the integer discriminant of `curve a₂ a₄ a₆`.
* `ECCompute.discrIntK`: its raw-primitive kernel twin.
* `ECCompute.fvalModP`: the label polynomial `f(θ)` reduced mod `p` in `Nat`.
* `ECCompute.checkLabel`, `ECCompute.checkLabels`: the kernel-reducible boolean checks.

Correctness is in `ECCompute.Soundness.Labels` (`descentHyp_of_checkLabel`, `checkLabels_true`).
-/

namespace ECCompute

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the case `a₁ = a₃ = 0`), matching
`WeierstrassCurve.Δ`. -/
def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

/-- The label polynomial `f(θ) = θ³ + a₂θ² + a₄θ + a₆` reduced mod `p` in `Nat` (θ and the
coefficients reduced to residues first). -/
noncomputable def fvalModP (a₂ a₄ a₆ θ : ℤ) (p : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.add
    (Nat.mul (Nat.mul (Int.emod θ p).toNat (Int.emod θ p).toNat) (Int.emod θ p).toNat)
    (Nat.mul (Int.emod a₂ p).toNat (Nat.mul (Int.emod θ p).toNat (Int.emod θ p).toNat)))
    (Nat.mul (Int.emod a₄ p).toNat (Int.emod θ p).toNat)) (Int.emod a₆ p).toNat) p

/-- `discrInt` written with the raw `Int.mul`/`Int.add`/`Int.sub`/`Int.neg` primitives, powers
expanded. -/
def discrIntK (a₂ a₄ a₆ : ℤ) : ℤ :=
  let b2 := Int.mul 4 a₂
  let b4 := Int.mul 2 a₄
  let b6 := Int.mul 4 a₆
  Int.add (Int.sub (Int.sub
      (Int.neg (Int.mul (Int.mul b2 b2)
        (Int.sub (Int.mul (Int.mul 4 a₂) a₆) (Int.mul a₄ a₄))))
      (Int.mul 8 (Int.mul (Int.mul b4 b4) b4)))
      (Int.mul 27 (Int.mul b6 b6)))
    (Int.mul (Int.mul (Int.mul 9 b2) b4) b6)

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ) : Bool :=
  ((Nat.beq (Nat.mod 6 p) 0).not').and'
    (((Int.beq' (Int.emod
      (discrIntK (Int.emod a₂ p) (Int.emod a₄ p) (Int.emod a₆ p)) p) 0).not').and'
      (Nat.beq (fvalModP a₂ a₄ a₆ θ p) 0))

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkLabel a₂ a₄ a₆ l.1 l.2) labels

end ECCompute
