/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 445 has rank at least 20

The elliptic curve recorded as
[curve 445](https://elliptic-rank.icarm.cloud/curve/445) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -90872683182171123779863585495688745`   and
  `a₆ = 10534068423995936974583664932054639017801516408581081`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 445 over `ℚ`. -/
@[expose] public def curve445 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -90872683182171123779863585495688745,
    10534068423995936974583664932054639017801516408581081⟩

/-- ICARM leaderboard curve 445 has Mordell-Weil rank at least `20`. -/
public theorem curve445_hasRankGE_20 : HasRankGE curve445 20 := by
  unfold curve445
  certify_curve torsion 59 "data/curve445.txt" "data/curve445-labels.txt"

/-- Curve 445 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve445.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 445. -/
public theorem curve445_j : curve445.j = 82989618253787008155744822565317045668508752752402426405871908814179934808740129247487938796856392988927128081 / 88829305886035909223406790580188831734489544997532961921266764802355273349240637700988946188606271946752 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
