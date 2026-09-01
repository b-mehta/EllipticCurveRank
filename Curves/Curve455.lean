/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 455 has rank at least 20

The elliptic curve recorded as
[curve 455](https://elliptic-rank.icarm.cloud/curve/455) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -51118531933701314117226670804090500`   and
  `a₆ = 4356025409211819471328533670264706621678809638000000`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 455 over `ℚ`. -/
@[expose] public def curve455 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -51118531933701314117226670804090500,
    4356025409211819471328533670264706621678809638000000⟩

/-- ICARM leaderboard curve 455 has Mordell-Weil rank at least `20`. -/
public theorem curve455_hasRankGE_20 : HasRankGE curve455 20 := by
  unfold curve455
  certify_curve torsion 47 "data/curve455.txt" "data/curve455-labels.txt"

/-- Curve 455 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve455.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 455. -/
public theorem curve455_j : curve455.j = 442796787758497179158231098715209043260023124263679502632603398402570467724870078827471394583563017296 / 10545295362814368663871632391921672527213129847450756372691622911356340910800942543841819137390625 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
