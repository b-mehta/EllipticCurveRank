/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 300 has rank at least 9

The elliptic curve recorded as
[curve 300](https://elliptic-rank.icarm.cloud/curve/300) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -550746640`   and
  `a₆ = 4883372708096`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 300 over `ℚ`. -/
@[expose] public def curve300 : WeierstrassCurve ℚ := ⟨1, 0, 0, -550746640, 4883372708096⟩

/-- ICARM leaderboard curve 300 has Mordell-Weil rank at least `9`. -/
public theorem curve300_hasRankGE_9 : HasRankGE curve300 9 := by
  unfold curve300
  certify_curve torsion 17 "data/curve300.txt" "data/curve300-labels.txt"

/-- Curve 300 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve300.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 300. -/
public theorem curve300_j : curve300.j = 18474780236578927166503532079361 / 389183972361856823597248512 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
