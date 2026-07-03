/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness
import ECCompute.ModelBridge
import ECCompute.QuickRfl
import Mathlib.Tactic.NormNum.Prime

/-!
# The Martin–McMillen curve has rank at least 23 (T10)

This file is the final instantiation of ECCompute: a fully machine-checked proof that the
Mordell–Weil group of the Martin–McMillen elliptic curve

  `E : y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `                    + 32685500727716376257923347071452044295907443056345614006`

over `ℚ` has rank at least `23`, i.e. `ECCompute.HasRankGE (toCurveQ 1 0 1 a₄ a₆) 23`.

The proof is a descent-character certificate in the sense of `ECCompute.Soundness`.  All numeric
data is produced on the **integral short model** `curve 1 A₄ A₆` with
`A₄ = 16a₄ + 8` and `A₆ = 64a₆ + 16`, to which the general model is carried by the group
isomorphism `ModelBridge.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`,
so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `rank23Pt` — the 23 points on the short model.  Fractional `x`-coordinates are stored in reduced
  `Rat.mk'` form so the kernel evaluates `lambdaCompute` on them by `rfl` (the smart constructor
  `_ / _` would leave a well-founded `Nat.gcd` the kernel cannot reduce).
* `rank23Lab` — the 23 descent columns `(p, θ)`, primes between `7` and `163`, following Cremona's
  worked example (§2.3 of *On the computation of Mordell–Weil and 2-Selmer groups*).
* `rank23Cert` — the certificate bundle; `matB` is the `23 × 23` descent-character matrix over `𝔽₂`
  and `matM` its inverse, both as `Nat` bitmasks (`F2Invert`).
* `martinMcMillen_hasRankGE_23` — the theorem, obtained by feeding `rank23Cert` to
  `rank_ge_of_certificate` and transporting the bound along `generalToShortEquiv`.

Every referee obligation is discharged by kernel computation (`rfl`) or `norm_num`; there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelBridge

/-- The `a₄` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₄ : ℤ := -19252966408674012828065964616418441723

/-- The `a₆` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₆ : ℤ := 32685500727716376257923347071452044295907443056345614006

/-- The `a₄` coefficient of the integral short model `curve 1 sA₄ sA₆` (`= 16·mmA₄ + 8`). -/
abbrev sA₄ : ℤ := -308047462538784205249055433862695067560

/-- The `a₆` coefficient of the integral short model `curve 1 sA₄ sA₆` (`= 64·mmA₆ + 16`). -/
abbrev sA₆ : ℤ := 2091872046573848080507094212572930834938076355606119296400

/-- The Martin–McMillen elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `              + 32685500727716376257923347071452044295907443056345614006`.

Certified to have Mordell–Weil rank at least `23` in `martinMcMillen_hasRankGE_23`. -/
def curveMartinMcMillen : WeierstrassCurve ℚ := toCurveQ 1 0 1 mmA₄ mmA₆

/-- A reduced-form `Rat.mk'` equals the corresponding division of numerator by denominator.
Used to rewrite the `Rat.mk'` `x`-coordinates back to `_ / _` form for `norm_num`. -/
theorem mk'_eq_div (a : ℤ) (b : ℕ) (h1 h2) : (Rat.mk' a b h1 h2 : ℚ) = (a : ℚ) / (b : ℚ) := by
  have := Rat.num_div_den (Rat.mk' a b h1 h2)
  simpa using this.symm

/-- The 23 rational points of the Martin–McMillen curve carried to the integral short model
`curve 1 sA₄ sA₆` by `(x, y) ↦ (4x, 8y + 4x + 4)`.  Fractional `x`-coordinates are in reduced
`Rat.mk'` form. -/
def rank23Pt : Fin 23 → ℚ × ℚ := ![
  ((10038235050769704300 : ℚ), (-3336710883046427160653004720 : ℚ)),
  ((-12609224276463955620 : ℚ), (63018561028024449536788756800 : ℚ)),
  ((62772116111964343440 : ℚ), (-479685804086960625011670772740 : ℚ)),
  ((Rat.mk' (-62742183048281960180) 9 (by norm_num) (by norm_num)),
   (1686273464073439053514480308400 / 27 : ℚ)),
  ((10795722929841531180 : ℚ), (4949035461599182052953062000 : ℚ)),
  ((12223314864270639180 : ℚ), (-12360800128808552821813062000 : ℚ)),
  ((20704428556473727080 : ℚ), (-67744832724908927786218689900 : ℚ)),
  ((15138072327630340620 : ℚ), (29961418695051471843326070960 : ℚ)),
  ((13502411194738397580 : ℚ), (19854019645350937993830920400 : ℚ)),
  ((201017040110885532780 : ℚ), (2839513262967491260401250599600 : ℚ)),
  ((-570783866185395540 : ℚ), (47618427211792501462719940080 : ℚ)),
  ((-12885261288808073700 : ℚ), (62624313919951372076005193280 : ℚ)),
  ((10151015303377981980 : ℚ), (3296929456755476538366427200 : ℚ)),
  ((10374683265900459180 : ℚ), (-3556177582428684015461802000 : ℚ)),
  ((14612491820978757864 : ℚ), (26658246869933046006709784340 : ℚ)),
  ((67655401894191072780 : ℚ), (-539376228512420618380334439600 : ℚ)),
  ((Rat.mk' 91407152955412578142189035 34304449 (by norm_num) (by norm_num)),
   (-7216319708485906545088530317097739217370 / 200921157793 : ℚ)),
  ((9274944718973638380 : ℚ), (-5711590488823968468396817200 : ℚ)),
  ((Rat.mk' 3419757374826200620 9 (by norm_num) (by norm_num)),
   (-1199868934926028516155152146000 / 27 : ℚ)),
  ((9166062171990879180 : ℚ), (6196136672536732797954858000 : ℚ)),
  ((-6890302234596363220 : ℚ), (-62348106242655695027970783600 : ℚ)),
  ((-20063626238798778852 : ℚ), (-13993804226515223141870819904 : ℚ)),
  ((Rat.mk' 4830330257017414393500 49 (by norm_num) (by norm_num)),
   (330719201912027805062057684602560 / 343 : ℚ))]

/-- The 23 descent-column labels `(p, θ)`: prime `p` (between `7` and `163`) and a root `θ` of the
short-model 2-division cubic modulo `p`. -/
def rank23Lab : Fin 23 → ℕ × ℤ := ![
  (7, 0), (7, 1), (31, 6), (43, 0), (47, 27), (53, 13), (53, 40), (59, 52), (67, 27), (71, 10),
  (83, 74), (89, 78), (97, 21), (109, 8), (113, 55), (127, 110), (131, 9), (131, 50), (139, 21),
  (149, 9), (151, 27), (157, 81), (163, 55)]

/-- The rank-23 certificate for the Martin–McMillen curve, on the integral short model
`curve 1 sA₄ sA₆`.  `matB` is the `23 × 23` descent-character matrix over `𝔽₂` (row bitmasks),
`matM` its inverse (column bitmasks); `t = 0` with torsion witness prime `29`. -/
def rank23Cert : Certificate where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := sA₄
  a₆ := sA₆
  rho := 23
  points := List.ofFn rank23Pt
  labels := List.ofFn rank23Lab
  matB := [7473342, 7551941, 3161895, 3710394, 3287852, 4373580, 5018546, 3669779, 8185065,
    5958582, 2607786, 4949490, 6461685, 1024421, 5071786, 3899507, 3380385, 7725498, 3045506,
    3140458, 1063523, 4372266, 4025296]
  matM := [2370869, 7665944, 3876357, 6048202, 5908841, 4816121, 1908375, 1476116, 1543552,
    5414431, 5679871, 7540436, 6420779, 4964488, 6356144, 7962535, 6764200, 4753997, 1453524,
    3753019, 8037412, 3876062, 155750]
  t := 0
  torsionPrime := 29

/-- Each listed short-model point lies on `curve 1 sA₄ sA₆`. -/
theorem rank23_hpt : ∀ i, (curve 1 sA₄ sA₆).toAffine.Equation
    (rank23Pt i).1 (rank23Pt i).2 := by
  intro i
  fin_cases i <;>
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [rank23Pt, curve, mk'_eq_div]
      norm_num

/-- Each label prime is prime. -/
theorem rank23_hlabP : ∀ j, ((rank23Lab j).1).Prime := by
  intro j
  fin_cases j <;> · rw [rank23Lab]; norm_num

/-- Each label passes the descent column-legitimacy check. -/
theorem rank23_hlabC : ∀ j, checkLabel rank23Cert.a₂ rank23Cert.a₄ rank23Cert.a₆
    (rank23Lab j).1 (rank23Lab j).2 = true := by
  intro j
  fin_cases j <;> quickRfl

/-- The `(i, j)` entry of `matB` is the computed descent character `λ_{pⱼ,θⱼ}(Pᵢ)`. -/
theorem rank23_hB : ∀ i j : Fin rank23Cert.rho,
    F2Invert.toMat rank23Cert.matB rank23Cert.rho i j =
      lambdaCompute rank23Cert.a₂ rank23Cert.a₄ rank23Cert.a₆ (rank23Lab j).1
        ((rank23Lab j).2 : ZMod (rank23Lab j).1) (rank23Pt i).1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The supplied inverse certifies `matB` is invertible over `𝔽₂`. -/
theorem rank23_hinv : F2Invert.checkInv rank23Cert.rho rank23Cert.matB rank23Cert.matM = true := by
  quickRfl

/-- The 2-division cubic has no root modulo the torsion witness prime `29` (so `t = 0`). -/
theorem rank23_htor :
    hasRootMod (4 * rank23Cert.a₂) (16 * rank23Cert.a₄) (64 * rank23Cert.a₆)
      rank23Cert.torsionPrime = false := by
  rw [← Bool.not_eq_true', ← Bool.not'_eq_not]
  quickRfl

/-- **The Martin–McMillen curve has Mordell–Weil rank at least 23.**  Fully certified: the descent
characters of the 23 points are `𝔽₂`-linearly independent (`matB` is invertible) and the curve has
no rational 2-torsion, so its rank over `ℚ` is at least `23`. -/
theorem martinMcMillen_hasRankGE_23 : HasRankGE curveMartinMcMillen 23 := by
  unfold curveMartinMcMillen
  have key : HasRankGE (curve rank23Cert.a₂ rank23Cert.a₄ rank23Cert.a₆)
      (rank23Cert.rho - rank23Cert.t) :=
    rank_ge_of_certificate rank23Cert rank23Pt rank23Lab rank23_hpt rank23_hlabP rank23_hlabC
      rank23_hB rank23_hinv rfl (by decide) rank23_htor
  have hbc : bridgeCurve 1 0 1 mmA₄ mmA₆ = curve rank23Cert.a₂ rank23Cert.a₄ rank23Cert.a₆ := by
    simp only [bridgeCurve, bridgeA₂, bridgeA₄, bridgeA₆, rank23Cert, curve, mmA₄, mmA₆, sA₄, sA₆]
    norm_num
  have hbridge : HasRankGE (bridgeCurve 1 0 1 mmA₄ mmA₆) 23 := by
    rw [hbc]; exact key
  exact hasRankGE_of_addEquiv (generalToShortEquiv 1 0 1 mmA₄ mmA₆) hbridge

end ECCompute
