/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 454 has rank at least 20

The elliptic curve recorded as
[curve 454](https://elliptic-rank.icarm.cloud/curve/454) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -131235162921679918505097922631000`   and
  `a₆ = 578061958908714844618861371898647409879281000000`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 454 over `ℚ`. -/
@[expose] public def curve454 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -131235162921679918505097922631000, 578061958908714844618861371898647409879281000000⟩

/-- ICARM leaderboard curve 454 has Mordell-Weil rank at least `20`. -/
public theorem curve454_hasRankGE_20 : HasRankGE curve454 20 := by
  unfold curve454
  certify_curve torsion 47 "data/curve454.txt" "data/curve454-labels.txt"

/-- Curve 454 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve454.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 454. -/
public theorem curve454_j : curve454.j = 249962210341771503786858124901118922587295056038084439634777222679991137490615447489886056429690864001 / 298825468998917412750017160115596332210490894333456031803464670941710970484839291899514880000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
