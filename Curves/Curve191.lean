/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 191 has rank at least 16

The elliptic curve recorded as
[curve 191](https://elliptic-rank.icarm.cloud/curve/191) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -60923262881679161131199816568720`   and
  `a₆ = 182435750535622934108717118205361600171372294400`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve191.txt`; descent labels are in
`data/curve191-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 191 over `ℚ`. -/
@[expose] public def curve191 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -60923262881679161131199816568720, 182435750535622934108717118205361600171372294400⟩

/-- ICARM leaderboard curve 191 has Mordell-Weil rank at least `16`. -/
public theorem curve191_hasRankGE_16 : HasRankGE curve191 16 := by
  unfold curve191
  certify_curve torsion 41 "data/curve191.txt" "data/curve191-labels.txt"

/-- Curve 191 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve191.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 191. -/
public theorem curve191_j : curve191.j = 25007666950555707589836157731796080400696061740143823847972988422635045355361076936306410035454132481 / 93858557525002069986716442228582690235767407598682422890314976013836608666063661484178636800000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
