/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 212 has rank at least 11

The elliptic curve recorded as
[curve 212](https://elliptic-rank.icarm.cloud/curve/212) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -221556180740323405132844117936`   and
  `a₆ = 35386140191724122461245294467670188433973860`

over `ℚ`. It has Mordell-Weil rank at least `11`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 212 over `ℚ`. -/
@[expose] public def curve212 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -221556180740323405132844117936, 35386140191724122461245294467670188433973860⟩

/-- ICARM leaderboard curve 212 has Mordell-Weil rank at least `11`. -/
public theorem curve212_hasRankGE_11 : HasRankGE curve212 11 := by
  unfold curve212
  certify_curve torsion 7 "data/curve212.txt" "data/curve212-labels.txt"

/-- Curve 212 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve212.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 212. -/
public theorem curve212_j : curve212.j = 1174560429575150237826421944015643285827315118865246188670602670464080987030718985375416516 / 151459489927613924435192147605383698237111010070861338842066555060058382601407336344525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
