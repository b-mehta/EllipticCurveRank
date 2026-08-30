/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 399 has rank at least 29

The elliptic curve recorded as
[curve 399](https://elliptic-rank.icarm.cloud/curve/399) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -11226388884183735861962205254536431339112877364056989183905`   and
  `a₆ = 4501942654827661251750083327723462246146953084820857257507906505001954118701`
  `     67825256777`

over `ℚ`. It has Mordell-Weil rank at least `29`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 399 over `ℚ`. -/
@[expose] public def curve399 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -11226388884183735861962205254536431339112877364056989183905,
    450194265482766125175008332772346224614695308482085725750790650500195411870167825256777⟩

/-- ICARM leaderboard curve 399 has Mordell-Weil rank at least `29`. -/
public theorem curve399_hasRankGE_29 : HasRankGE curve399 29 := by
  unfold curve399
  certify_curve torsion 23 "data/curve399.txt" "data/curve399-labels.txt"

/-- Curve 399 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve399.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 399. -/
public theorem curve399_j : curve399.j = 437188684191191329419051560262769632314122311426391061750188953513895819485309130341775205234871278129723879062442823919381431850599986533448058086478592415380583566287209111 / 8373328809141570627744295436754675435126424344412932312627882994186135708417193313638867664226162941437691389945083825270256273412447381546091107006738351454420992000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
