/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 418 has rank at least 21

The elliptic curve recorded as
[curve 418](https://elliptic-rank.icarm.cloud/curve/418) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -815073141784200754215404771679519674339839601501320`   and
  `a₆ = 1014873432286428365761822621820035236319327526169441740508116453318126183840`
  `     0`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 418 over `ℚ`. -/
@[expose] public def curve418 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -815073141784200754215404771679519674339839601501320,
    10148734322864283657618226218200352363193275261694417405081164533181261838400⟩

/-- ICARM leaderboard curve 418 has Mordell-Weil rank at least `21`. -/
public theorem curve418_hasRankGE_21 : HasRankGE curve418 21 := by
  unfold curve418
  certify_curve torsion 31 "data/curve418.txt" "data/curve418-labels.txt"

/-- Curve 418 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve418.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 418. -/
public theorem curve418_j : curve418.j = -59884366515826034081632782375386446635304298063942770264211162041015621035451612060698302685753477296144763899728934606036481535288506066228589507565840714881 / 9839316513169517755920678269709069435748137552838716848014248656337848459529179209312843801536495603592215241976105162110825387465187436111452309913600000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
