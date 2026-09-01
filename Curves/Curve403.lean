/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 403 has rank at least 28

The elliptic curve recorded as
[curve 403](https://elliptic-rank.icarm.cloud/curve/403) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -4789549597347342217921487845151485156552215088671735288`   and
  `a₆ = 4038895070100529332977411476954657751699524878306148134823129956225541669799`
  `     702592`

over `ℚ`. It has Mordell-Weil rank at least `28`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 403 over `ℚ`. -/
@[expose] public def curve403 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -4789549597347342217921487845151485156552215088671735288,
    4038895070100529332977411476954657751699524878306148134823129956225541669799702592⟩

/-- ICARM leaderboard curve 403 has Mordell-Weil rank at least `28`. -/
public theorem curve403_hasRankGE_28 : HasRankGE curve403 28 := by
  unfold curve403
  certify_curve torsion 23 "data/curve403.txt" "data/curve403-labels.txt"

/-- Curve 403 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve403.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 403. -/
public theorem curve403_j : curve403.j = -1327874340493709122356997953600721639363180109006192420792870013328355734429748206853823373263641882589289495053414255721893781023314985695458557612267942497267425 / 1673717890935740430117253334012118857534901797650736306634233454928964135797166218092801498769461043659983593771528973721120197338567833160806336371770294272 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
