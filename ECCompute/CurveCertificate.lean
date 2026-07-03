/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness
import ECCompute.ModelChange
import ECCompute.CheckMatrix
import ECCompute.QuickRfl
import ECCompute.Primes
import Mathlib.Tactic.NormNum.Prime

/-!
# The front door for a rank certificate

`ECCompute.Soundness.rank_ge_of_certificate` proves a rank lower bound on the *short integral model*
`curve c.a₂ c.a₄ c.a₆`, where the descent character lives.  A concrete curve is usually given by a
*general* integral Weierstrass model `toCurveQ a₁ a₂ a₃ a₄ a₆`; `ModelChange.generalToShortEquiv`
carries it to the short model `intShortModel a₁ a₂ a₃ a₄ a₆` by completing the square and scaling.

`hasRankGE_of_certificate` bolts these two together, so each instantiation only has to supply the
certificate data, the six referee facts, and the single equation identifying the certificate's short
model with the target of the change of variables.  It replaces the roughly ten-line "unfold,
assemble, transport" tail that every curve file would otherwise repeat.  `mk'_eq_div` is the small
`Rat.mk'` rewrite the point-on-curve checks need, hoisted here so it is stated once.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- A reduced-form `Rat.mk'` equals the corresponding division of numerator by denominator.  Used to
rewrite the `Rat.mk'` `x`-coordinates of certificate points back to `_ / _` form for the
point-on-curve check. -/
theorem mk'_eq_div (a : ℤ) (b : ℕ) (h1 h2) : (Rat.mk' a b h1 h2 : ℚ) = (a : ℚ) / (b : ℚ) := by
  have := Rat.num_div_den (Rat.mk' a b h1 h2)
  simpa using this.symm

/-- **The certified rank lower bound for a general integral model.**  Given a certificate `c` whose
short model `curve c.a₂ c.a₄ c.a₆` is the change-of-variables target of the general model
`toCurveQ a₁ a₂ a₃ a₄ a₆` (the equation `hmodel`), and the six referee facts of
`rank_ge_of_certificate`, the Mordell–Weil rank of `toCurveQ a₁ a₂ a₃ a₄ a₆` over `ℚ` is at least
`c.rho - c.t`.  The bound is proven on the short model and transported along
`generalToShortEquiv`. -/
theorem hasRankGE_of_certificate (a₁ a₂ a₃ a₄ a₆ : ℤ) (c : Certificate)
    (pt : Fin c.rho → ℚ × ℚ) (lab : Fin c.rho → ℕ × ℤ)
    (hmodel : intShortModel a₁ a₂ a₃ a₄ a₆ = curve c.a₂ c.a₄ c.a₆)
    (hpt : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2)
    (hlabP : ∀ j, ((lab j).1).Prime)
    (hlabC : ∀ j, checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 = true)
    (hB : ∀ i j : Fin c.rho,
        F2Invert.toMat c.matB c.rho i j
          = lambdaCompute c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1)
    (hinv : F2Invert.checkInv c.rho c.matB c.matM = true)
    (ht : c.t = 0)
    (htorP : c.torsionPrime ≠ 0)
    (htor : hasRootMod (4 * c.a₂) (16 * c.a₄) (64 * c.a₆) c.torsionPrime = false) :
    HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) (c.rho - c.t) := by
  have key : HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) :=
    rank_ge_of_certificate c pt lab hpt hlabP hlabC hB hinv ht htorP htor
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
