/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 160 has rank at least 19

The elliptic curve recorded as
[curve 160](https://elliptic-rank.icarm.cloud/curve/160) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -73218567298360414151945259`   and
  `a₆ = 245000581765085750173970908953765294265`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by cocoxhuang.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 160 over `ℚ`. -/
@[expose] public def curve160 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -73218567298360414151945259, 245000581765085750173970908953765294265⟩

/-- ICARM leaderboard curve 160 has Mordell-Weil rank at least `19`. -/
public theorem curve160_hasRankGE_19 : HasRankGE curve160 19 := by
  unfold curve160
  certify_curve torsion 61 "data/curve160.txt" "data/curve160-labels.txt"

/-- Curve 160 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve160.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 160. -/
public theorem curve160_j : curve160.j = -59546996862613172299059277421620438364212604366648944777538524529047394936841649 / 1110471669081969085126829746172651769282872411042233998981380763261191722500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
