/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 67 has rank at least 27

The elliptic curve recorded as
[curve 67](https://elliptic-rank.icarm.cloud/curve/67) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -55671146865244401916117773020296610079754015500970`   and
  `a₆ = 161981895322788558220906653027519611838007321625214218991719656790551905956`

over `ℚ`. It has Mordell-Weil rank at least `27`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 67 over `ℚ`. -/
@[expose] public def curve067 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -55671146865244401916117773020296610079754015500970,
    161981895322788558220906653027519611838007321625214218991719656790551905956⟩

/-- ICARM leaderboard curve 67 has Mordell-Weil rank at least `27`. -/
public theorem curve067_hasRankGE_27 : HasRankGE curve067 27 := by
  unfold curve067
  certify_curve torsion 47 "data/curve067.txt" "data/curve067-labels.txt"

/-- Curve 67 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve067.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 67. -/
public theorem curve067_j : curve067.j = -19081574911308163519167857789930910431513370348120735399409672042058680390500520014879931412709582756211224505999425328544286863936085602605756678108056481 / 292295992467036730780372591065803086322380999542983847983425194363595329691796423905092278238635719085287829796511182852120658943291432879857572200448 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
