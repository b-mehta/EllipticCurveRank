/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 459 has rank at least 20

The elliptic curve recorded as
[curve 459](https://elliptic-rank.icarm.cloud/curve/459) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1928281706386442181413475191954491925`   and
  `a₆ = 1041272774542851005444015987964798785676127762575830625`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 459 over `ℚ`. -/
@[expose] public def curve459 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1928281706386442181413475191954491925,
    1041272774542851005444015987964798785676127762575830625⟩

/-- ICARM leaderboard curve 459 has Mordell-Weil rank at least `20`. -/
public theorem curve459_hasRankGE_20 : HasRankGE curve459 20 := by
  unfold curve459
  certify_curve torsion 19 "data/curve459.txt" "data/curve459-labels.txt"

/-- Curve 459 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve459.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 459. -/
public theorem curve459_j : curve459.j = -15654167745497069840292515834611261693842463335829662218578748738507310767329615359996524878268539438917283717 / 188018734311187398024989935243541066804975128206807508184988540281668993245613061467077444905797632000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
