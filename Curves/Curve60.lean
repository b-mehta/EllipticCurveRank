/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 60 has rank at least 10

The elliptic curve recorded as
[curve 60](https://elliptic-rank.icarm.cloud/curve/60) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1536664`   and
  `a₆ = 648294124`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve60.txt`; descent labels are in
`data/curve60-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 60 over `ℚ`. -/
@[expose] public def curve60 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1536664, 648294124⟩

/-- ICARM leaderboard curve 60 has Mordell-Weil rank at least `10`. -/
public theorem curve60_hasRankGE_10 : HasRankGE curve60 10 := by
  unfold curve60
  certify_curve torsion 13 "data/curve60.txt" "data/curve60-labels.txt"

/-- Curve 60 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve60.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 60. -/
public theorem curve60_j : curve60.j = 401292111107210344394841 / 50881111474471687972 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
