/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness
import ECCompute.ModelBridge
import ECCompute.QuickRfl
import ECCompute.CheckMatrix
import Mathlib.Tactic.NormNum.Prime

/-!
# A second curve of rank at least 29

This file is a second full instantiation of ECCompute: a machine-checked proof that the
Mordell–Weil group of the elliptic curve

  `E : y² + xy = x³ + a₄ x + a₆`

over `ℚ` (with the large integer coefficients `a₄`, `a₆` below) has rank at least `29`, i.e.
`ECCompute.HasRankGE (toCurveQ 1 0 0 a₄ a₆) 29`.

The proof is a descent-character certificate in the sense of `ECCompute.Soundness`, following
`ECCompute.RankTwentyThree` line for line. All numeric data is produced on the **integral short
model** `curve 1 A₄ A₆` with `A₄ = 16a₄` and `A₆ = 64a₆` (here `a₁ = 1`, `a₂ = a₃ = 0`, so the
`b`-invariant shifts vanish), to which the general model is carried by the group isomorphism
`ModelBridge.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`, so a
rational point `(x, y)` maps to `(4x, 8y + 4x)`).

* `rank29Pt` — the 29 points on the short model. The one fractional `x`-coordinate is stored in
  reduced `Rat.mk'` form so the kernel evaluates `lambdaCompute` on it by `rfl`.
* `rank29Lab` — the 29 descent columns `(p, θ)`, primes between `19` and `179`, matching Cremona's
  descent-image output for this curve.
* `rank29Cert` — the certificate bundle; `matB` is the `29 × 29` descent-character matrix over `𝔽₂`
  and `matM` its inverse, both as `Nat` bitmasks (`F2Invert`).
* `elkiesKlagsbrun_hasRankGE_29` — the theorem, obtained by feeding `rank29Cert` to
  `rank_ge_of_certificate` and transporting the bound along `generalToShortEquiv`.

Every referee obligation is discharged by kernel computation (`rfl`) or `norm_num`; there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelBridge

-- The `rfl` certificate checks (`checkInv`, the `matB` entries) reduce large `Nat` recursions in
-- the elaborator, so raise the recursion limit for the whole file.
set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₄ : ℤ := -27006183241630922218434652145297453784768054621836357954737385

/-- The `a₆` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₆ : ℤ :=
  55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- The `a₄` coefficient of the integral short model `curve 1 ekShortA₄ ekShortA₆` (`= 16·ekA₄`). -/
abbrev ekShortA₄ : ℤ := -432098931866094755494954434324759260556288873949381727275798160

/-- The `a₆` coefficient of the integral short model `curve 1 ekShortA₄ ekShortA₆` (`= 64·ekA₆`). -/
abbrev ekShortA₆ : ℤ :=
  3536515747285912094447148773831564276577348290082245094935833905865562449773835099240750175808

/-- The Elkies–Klagsbrun rank-29 elliptic curve over `ℚ` (general model)

  `y² + xy = x³ + ekA₄ x + ekA₆`.

Certified to have Mordell–Weil rank at least `29` in `elkiesKlagsbrun_hasRankGE_29`. -/
def curveElkiesKlagsbrun : WeierstrassCurve ℚ := toCurveQ 1 0 0 ekA₄ ekA₆

/-- A reduced-form `Rat.mk'` equals the corresponding division of numerator by denominator.
Used to rewrite the `Rat.mk'` `x`-coordinate back to `_ / _` form for `norm_num`. -/
private theorem mk'_eq_div (a : ℤ) (b : ℕ) (h1 h2) :
    (Rat.mk' a b h1 h2 : ℚ) = (a : ℚ) / (b : ℚ) := by
  have := Rat.num_div_den (Rat.mk' a b h1 h2)
  simpa using this.symm

/-- The 29 rational points of the second curve carried to the integral short model
`curve 1 ekShortA₄ ekShortA₆` by `(x, y) ↦ (4x, 8y + 4x)`.  The one fractional `x`-coordinate is
in reduced `Rat.mk'` form. -/
def rank29Pt : Fin 29 → ℚ × ℚ := ![
  ((11564781896914148757833022146536 : ℚ), (9279445984769009216460584199967307269769548800 : ℚ)),
  ((13610168661288511245805938568936 : ℚ), (13292065785317542057069922278354970291980896000 : ℚ)),
  ((17195040106233868961688430259176 : ℚ), (34505137999121906833368000532948223471850055680 : ℚ)),
  ((14915026671083788039537822858216 : ℚ), (20241441756677887643958900632041323903106037760 : ℚ)),
  ((23966976528208312922044740520936 : ℚ), (83351213030736298865386712654139327398491392000 : ℚ)),
  ((12945974138531074082160908892136 : ℚ), (10597014370097350895243636118403696763898854400 : ℚ)),
  ((312906744539964696929522757544936 : ℚ),
   (5523153680502079484934181772968831169518857984000 : ℚ)),
  ((45970422574195437498542420560936 : ℚ), (284290535291607663214115568101905146779372088000 : ℚ)),
  ((-20573213449536919219624352474264 : ℚ), (60978852088863874339749369308475225817426473600 : ℚ)),
  ((1775942622300261741126273740008 : ℚ), (52675744995110870761661053817410200051358702848 : ℚ)),
  ((-3918260075617078723010518999064 : ℚ), (71898787376836297561473575892633586060138368000 : ℚ)),
  ((20739577140848712998265845047336 : ℚ), (59124294304025222349762776566279877269888891200 : ℚ)),
  ((-17876684094748586008268718448664 : ℚ), (74485271142731653596381674350550642958597196800 : ℚ)),
  ((14425623340443701929802091880936 : ℚ), (17469157335853643485484637990825770123115072000 : ℚ)),
  ((64606978307141270930755972648936 : ℚ), (495271056739778776179137581352917582465950336000 : ℚ)),
  ((14294737423775065551849451479016 : ℚ), (16755737240926009693561802044338174293933552640 : ℚ)),
  ((-3037504199755432665745966576664 : ℚ), (69433369083665574529807993538967828741650380800 : ℚ)),
  ((-21312234879743544728424012477464 : ℚ), (55364705179035959753388604715395268985782323200 : ℚ)),
  ((21521073899581509422332158778216 : ℚ), (64845281920240222260674845959936817499007077760 : ℚ)),
  ((68276933949700392355760812993936 : ℚ), (540669418182362461987873497743687503967105079000 : ℚ)),
  ((20861730169613723032992203135176 : ℚ), (60012125969637755709103857280635659346153652320 : ℚ)),
  ((11355768712184096159054769728488 : ℚ), (9698770247716733827322118588452204655635392512 : ℚ)),
  ((Rat.mk' 972587529581528063785465619232616 81 (by norm_num) (by norm_num)),
   ((6493002177285819410882071323251994112123229958400 : ℚ) / (729 : ℚ))),
  ((10232916067358044599325040323048 : ℚ), (13652787166640650188016109311111661002237420032 : ℚ)),
  ((9445015771622403243910226690536 : ℚ), (17260027169948429035406580336888914016616819200 : ℚ)),
  ((10713248310579726732457759624936 : ℚ), (11701778888166382207180530047513821378140576000 : ℚ)),
  ((13517588339708923640339410415608 : ℚ), (12867953338876621481473581215717307942337245648 : ℚ)),
  ((14529630923483995671649965422056 : ℚ), (18045239496301620945456190533480624077139125760 : ℚ)),
  ((9715113053110087838172175720936 : ℚ), (15986600188884838564406951553982780598851008000 : ℚ))]

/-- The 29 descent-column labels `(p, θ)`: prime `p` (between `19` and `179`) and a root `θ` of the
short-model 2-division cubic modulo `p`. -/
def rank29Lab : Fin 29 → ℕ × ℤ := ![
  (19, 3), (19, 4), (23, 5), (23, 8), (29, 9), (37, 2), (37, 11), (47, 17), (53, 14), (59, 9),
  (59, 14), (73, 55), (79, 59), (83, 81), (97, 39), (101, 34), (103, 65), (107, 29), (107, 91),
  (109, 89), (127, 45), (127, 102), (131, 109), (151, 4), (157, 73), (163, 56), (173, 72),
  (173, 115), (179, 43)]

/-- The rank-29 certificate for the second curve, on the integral short model
`curve 1 ekShortA₄ ekShortA₆`.
`matB` is the `29 × 29` descent-character matrix over `𝔽₂` (row bitmasks), `matM` its inverse
(column bitmasks); `t = 0` with torsion witness prime `67`. -/
def rank29Cert : Certificate where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := ekShortA₄
  a₆ := ekShortA₆
  rho := 29
  points := List.ofFn rank29Pt
  labels := List.ofFn rank29Lab
  matB := [362692388, 180762173, 414259584, 483975833, 281259643, 305445451, 134953801, 523725317,
    458987003, 134888953, 46359831, 397323421, 160633099, 150343368, 34747304, 376567236,
    445638067, 409691202, 40918244, 6235769, 472209994, 67072530, 323393023, 321958794, 453383836,
    88056293, 114414568, 373488813, 449764306]
  matM := [200517310, 58058590, 336938950, 46971675, 117170164, 299595453, 215082071, 279412193,
    45578083, 293074749, 360916341, 157592411, 116643666, 465317890, 295867323, 71135259,
    125207482, 460997230, 280786175, 485150360, 226837813, 392096532, 444287549, 209135209,
    148917876, 516299009, 530074807, 471509895, 373043118]
  t := 0
  torsionPrime := 67

/-- Each listed short-model point lies on `curve 1 ekShortA₄ ekShortA₆`. -/
theorem rank29_hpt : ∀ i, (curve 1 ekShortA₄ ekShortA₆).toAffine.Equation
    (rank29Pt i).1 (rank29Pt i).2 := by
  intro i
  fin_cases i <;>
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [rank29Pt, curve, mk'_eq_div]
      decide +kernel

/-- Each label prime is prime. -/
theorem rank29_hlabP : ∀ j, ((rank29Lab j).1).Prime := by
  intro j
  fin_cases j <;> · rw [rank29Lab]; decide +kernel

/-- Each label passes the descent column-legitimacy check. -/
theorem rank29_hlabC : ∀ j, checkLabel rank29Cert.a₂ rank29Cert.a₄ rank29Cert.a₆
    (rank29Lab j).1 (rank29Lab j).2 = true := by
  intro j
  fin_cases j <;> quickRfl

/-- The `(i, j)` entry of `matB` is the computed descent character `λ_{pⱼ,θⱼ}(Pᵢ)`. -/
theorem rank29_hB : ∀ i j : Fin rank29Cert.rho,
    F2Invert.toMat rank29Cert.matB rank29Cert.rho i j =
      lambdaCompute rank29Cert.a₂ rank29Cert.a₄ rank29Cert.a₆ (rank29Lab j).1
        ((rank29Lab j).2 : ZMod (rank29Lab j).1) (rank29Pt i).1 :=
  checkB_true (by quickRfl)

/-- The supplied inverse certifies `matB` is invertible over `𝔽₂`. -/
theorem rank29_hinv : F2Invert.checkInv rank29Cert.rho rank29Cert.matB rank29Cert.matM = true := by
  quickRfl

/-- The 2-division cubic has no root modulo the torsion witness prime `67` (so `t = 0`). -/
theorem rank29_htor :
    hasRootMod (4 * rank29Cert.a₂) (16 * rank29Cert.a₄) (64 * rank29Cert.a₆)
      rank29Cert.torsionPrime = false := by
  rw [← Bool.not_eq_true', ← Bool.not'_eq_not]
  quickRfl

/-- **The Elkies–Klagsbrun curve has Mordell–Weil rank at least 29.**  Fully certified: the descent
characters of the 29 points are `𝔽₂`-linearly independent (`matB` is invertible) and the curve has
no rational 2-torsion, so its rank over `ℚ` is at least `29`. -/
theorem elkiesKlagsbrun_hasRankGE_29 : HasRankGE curveElkiesKlagsbrun 29 := by
  unfold curveElkiesKlagsbrun
  have key : HasRankGE (curve rank29Cert.a₂ rank29Cert.a₄ rank29Cert.a₆)
      (rank29Cert.rho - rank29Cert.t) :=
    rank_ge_of_certificate rank29Cert rank29Pt rank29Lab rank29_hpt rank29_hlabP rank29_hlabC
      rank29_hB rank29_hinv rfl (by decide) rank29_htor
  have hbc : bridgeCurve 1 0 0 ekA₄ ekA₆ = curve rank29Cert.a₂ rank29Cert.a₄ rank29Cert.a₆ := by
    simp only [bridgeCurve, bridgeA₂, bridgeA₄, bridgeA₆, rank29Cert, curve, ekA₄, ekA₆, ekShortA₄,
      ekShortA₆]
    norm_num
  have hbridge : HasRankGE (bridgeCurve 1 0 0 ekA₄ ekA₆) 29 := by
    rw [hbc]; exact key
  exact hasRankGE_of_addEquiv (generalToShortEquiv 1 0 0 ekA₄ ekA₆) hbridge

end ECCompute
