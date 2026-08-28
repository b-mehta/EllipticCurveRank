/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 171 has rank at least 16

The elliptic curve recorded as
[curve 171](https://elliptic-rank.icarm.cloud/curve/171) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -243033127794890100145570`   and
  `a₆ = 46065726780475015041673462927320900`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve171.txt`; descent labels are in
`data/curve171-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 171 over `ℚ`. -/
@[expose] public def curve171 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -243033127794890100145570, 46065726780475015041673462927320900⟩

/-- ICARM leaderboard curve 171 has Mordell-Weil rank at least `16`. -/
public theorem curve171_hasRankGE_16 : HasRankGE curve171 16 := by
  unfold curve171
  certify_curve torsion 7 "data/curve171.txt" "data/curve171-labels.txt"

/-- Curve 171 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve171.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 171. -/
public theorem curve171_j : curve171.j = 1587523419414951143821855709654276041720141093999092753162349373194132526881 / 1979571123617220930817947516260302552311906430241986844098656704000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
