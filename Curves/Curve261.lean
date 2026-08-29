/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 261 has rank at least 8

The elliptic curve recorded as
[curve 261](https://elliptic-rank.icarm.cloud/curve/261) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -14926`   and
  `a₆ = 2493976`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve261.txt`; descent labels are in
`data/curve261-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 261 over `ℚ`. -/
@[expose] public def curve261 : WeierstrassCurve ℚ := ⟨1, -1, 0, -14926, 2493976⟩

/-- ICARM leaderboard curve 261 has Mordell-Weil rank at least `8`. -/
public theorem curve261_hasRankGE_8 : HasRankGE curve261 8 := by
  unfold curve261
  certify_curve torsion 5 "data/curve261.txt" "data/curve261-labels.txt"

/-- Curve 261 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve261.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 261. -/
public theorem curve261_j : curve261.j = -367764996079095993 / 2466142200784916 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
