/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 209 has rank at least 13

The elliptic curve recorded as
[curve 209](https://elliptic-rank.icarm.cloud/curve/209) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -29618038071513025683295304897830`   and
  `a₆ = 61324180930341609392295317188644303710246778852`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 209 over `ℚ`. -/
@[expose] public def curve209 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -29618038071513025683295304897830, 61324180930341609392295317188644303710246778852⟩

/-- ICARM leaderboard curve 209 has Mordell-Weil rank at least `13`. -/
public theorem curve209_hasRankGE_13 : HasRankGE curve209 13 := by
  unfold curve209
  certify_curve torsion 7 "data/curve209.txt" "data/curve209-labels.txt"

/-- Curve 209 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve209.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 209. -/
public theorem curve209_j : curve209.j = 100604907018216673558266200465187546539410005976586291375160761720231536253102042904562947710161 / 1338564298715068084238032509236132656932831181570255662241548306776016518665875079823360000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
