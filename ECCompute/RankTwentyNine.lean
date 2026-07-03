/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

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
`ModelChange.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`, so a
rational point `(x, y)` maps to `(4x, 8y + 4x)`).

* `rank29Pt` — the 29 points on the short model. The one fractional `x`-coordinate is stored in
  reduced `Rat.mk'` form so the kernel evaluates `lambdaCompute` on it by `rfl`.
* `rank29Lab` — the 29 descent columns `(p, θ)`, primes between `19` and `179`, matching Cremona's
  descent-image output for this curve.
* `elkiesKlagsbrun_hasRankGE_29` — the theorem.  The `certify_curve` tactic computes the `29 × 29`
  descent-character matrix over `𝔽₂` (and its inverse) from the points and labels, assembles the
  certificate, and transports the bound to the general model.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

-- The `rfl` certificate checks (`checkInv`, the `matB` entries) reduce large `Nat` recursions in
-- the elaborator, so raise the recursion limit for the whole file.
set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₄ : ℤ := -27006183241630922218434652145297453784768054621836357954737385

/-- The `a₆` coefficient of the Elkies–Klagsbrun rank-29 curve (general model). -/
abbrev ekA₆ : ℤ :=
  55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- The Elkies–Klagsbrun rank-29 elliptic curve over `ℚ` (general model)

  `y² + xy = x³ + ekA₄ x + ekA₆`.

Certified to have Mordell–Weil rank at least `29` in `elkiesKlagsbrun_hasRankGE_29`. -/
def curveElkiesKlagsbrun : WeierstrassCurve ℚ := toCurveQ 1 0 0 ekA₄ ekA₆

/-- The 29 rational points of the second curve carried to the integral short model
`curve 1 (16·ekA₄) (64·ekA₆)` by `(x, y) ↦ (4x, 8y + 4x)`.  The one fractional `x`-coordinate is
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

/-- **The Elkies–Klagsbrun curve has Mordell–Weil rank at least 29.**  Fully certified by
`certify_curve`, which computes the `29 × 29` descent-character matrix (and its `𝔽₂` inverse) from
the points and labels, then discharges every referee obligation by kernel computation: the descent
characters of the 29 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion
(witnessed by the prime `67`), so its rank over `ℚ` is at least `29`. -/
theorem elkiesKlagsbrun_hasRankGE_29 : HasRankGE curveElkiesKlagsbrun 29 := by
  unfold curveElkiesKlagsbrun
  certify_curve coeffs 1 0 0 ekA₄ ekA₆ torsion 67 points rank29Pt labels rank29Lab

end ECCompute
