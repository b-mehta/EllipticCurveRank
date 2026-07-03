/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

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
isomorphism `ModelChange.generalToShortEquiv` (complete the square, then scale `(x, y) ↦ (4x, 8y)`,
so a rational point `(x, y)` maps to `(4x, 8y + 4x + 4)`).

* `rank23Pt` — the 23 points on the short model.  Fractional `x`-coordinates are stored in reduced
  `Rat.mk'` form so the kernel evaluates `lambdaCompute` on them by `rfl` (the smart constructor
  `_ / _` would leave a well-founded `Nat.gcd` the kernel cannot reduce).
* `rank23Lab` — the 23 descent columns `(p, θ)`, primes between `7` and `163`, following Cremona's
  worked example (§2.3 of *On the computation of Mordell–Weil and 2-Selmer groups*).
* `martinMcMillen_hasRankGE_23` — the theorem.  The `certify_curve` tactic computes the `23 × 23`
  descent-character matrix over `𝔽₂` (and its inverse) from the points and labels, assembles the
  certificate, and transports the bound to the general model.

Every referee obligation is discharged by kernel computation (`rfl`/`decide +kernel`); there is no
`native_decide`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- The `a₄` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₄ : ℤ := -19252966408674012828065964616418441723

/-- The `a₆` coefficient of the Martin–McMillen curve (general model). -/
abbrev mmA₆ : ℤ := 32685500727716376257923347071452044295907443056345614006


/-- The Martin–McMillen elliptic curve over `ℚ` (general model)

  `y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `              + 32685500727716376257923347071452044295907443056345614006`.

Certified to have Mordell–Weil rank at least `23` in `martinMcMillen_hasRankGE_23`. -/
def curveMartinMcMillen : WeierstrassCurve ℚ := toCurveQ 1 0 1 mmA₄ mmA₆

/-- The 23 rational points of the Martin–McMillen curve carried to the integral short model
`curve 1 (16·mmA₄+8) (64·mmA₆+16)` by `(x, y) ↦ (4x, 8y + 4x + 4)`.  Fractional `x`-coordinates
are in reduced `Rat.mk'` form. -/
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

/-- **The Martin–McMillen curve has Mordell–Weil rank at least 23.**  Fully certified by
`certify_curve`, which computes the `23 × 23` descent-character matrix (and its `𝔽₂` inverse) from
the points and labels, then discharges every referee obligation by kernel computation: the descent
characters of the 23 points are `𝔽₂`-linearly independent and the curve has no rational 2-torsion
(witnessed by the prime `29`), so its rank over `ℚ` is at least `23`. -/
theorem martinMcMillen_hasRankGE_23 : HasRankGE curveMartinMcMillen 23 := by
  unfold curveMartinMcMillen
  certify_curve coeffs 1 0 1 mmA₄ mmA₆ torsion 29 points rank23Pt labels rank23Lab

end ECCompute
