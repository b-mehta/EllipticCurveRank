/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 296 has rank at least 19

The elliptic curve recorded as
[curve 296](https://elliptic-rank.icarm.cloud/curve/296) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -319020439671592793251066477890`   and
  `a₆ = 66819798277603180086575284892786103016220100`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve296.txt`; descent labels are in
`data/curve296-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 296 over `ℚ`. -/
@[expose] public def curve296 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -319020439671592793251066477890, 66819798277603180086575284892786103016220100⟩

/-- ICARM leaderboard curve 296 has Mordell-Weil rank at least `19`. -/
public theorem curve296_hasRankGE_19 : HasRankGE curve296 19 := by
  unfold curve296
  certify_curve torsion 31 "data/curve296.txt" "data/curve296-labels.txt"

/-- Curve 296 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve296.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 296. -/
public theorem curve296_j : curve296.j = 3590700976825752743854876358474687348543624308767825369888944619989633728777546325940149379361 / 149121443298229386052318979969123375106547503463352849487930935295933405263138806456320000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
