/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 313 has rank at least 15

The elliptic curve recorded as
[curve 313](https://elliptic-rank.icarm.cloud/curve/313) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -220168815383488457944879718815779326933313515572495053707`   and
  `a₆ = 1257194842755882887406594337014748119778734089385499851686385036711122100696`
  `     018139931`

over `ℚ`. It has Mordell-Weil rank at least `15`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 313 over `ℚ`. -/
@[expose] public def curve313 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -220168815383488457944879718815779326933313515572495053707,
    1257194842755882887406594337014748119778734089385499851686385036711122100696018139931⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 313 has Mordell-Weil rank at least `15`. -/
public theorem curve313_hasRankGE_15 : HasRankGE curve313 15 := by
  unfold curve313
  certify_curve oneTorsion 34644294343055851339312808364 41 "data/curve313.txt" "data/curve313-labels.txt"

/-- Curve 313 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve313.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 313. -/
public theorem curve313_j : curve313.j = 720194356635719951533101653137209061878059386690033179510167171306208169372776040580958099414307248503139415196442408171638317834397905582725538536885312062851898699 / 152044075003078385471143574252115857645844804437204323025091724278740441023346870874213109827712856051230499408777677941456682101561395172046161966182400000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
