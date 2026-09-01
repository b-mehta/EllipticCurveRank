/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 428 has rank at least 21

The elliptic curve recorded as
[curve 428](https://elliptic-rank.icarm.cloud/curve/428) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -24917238940622813301347573754793308`   and
  `a₆ = 1527468176676160166289505293787711918102662665461488`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 428 over `ℚ`. -/
@[expose] public def curve428 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -24917238940622813301347573754793308,
    1527468176676160166289505293787711918102662665461488⟩

/-- ICARM leaderboard curve 428 has Mordell-Weil rank at least `21`. -/
public theorem curve428_hasRankGE_21 : HasRankGE curve428 21 := by
  unfold curve428
  certify_curve torsion 23 "data/curve428.txt" "data/curve428-labels.txt"

/-- Curve 428 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve428.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 428. -/
public theorem curve428_j : curve428.j = -4453601144423963885032970542578214569203365048653966913842008779864647667332347050499080986302069200 / 46395219715652421386319098299246051950996876961641976094875321792019334549826183001285426194947 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
