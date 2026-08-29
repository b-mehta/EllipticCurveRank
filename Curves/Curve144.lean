/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 144 has rank at least 9

The elliptic curve recorded as
[curve 144](https://elliptic-rank.icarm.cloud/curve/144) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -1996617`   and
  `a₆ = 1025754145`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve144.txt`; descent labels are in
`data/curve144-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 144 over `ℚ`. -/
@[expose] public def curve144 : WeierstrassCurve ℚ := ⟨0, 0, 0, -1996617, 1025754145⟩

/-- ICARM leaderboard curve 144 has Mordell-Weil rank at least `9`. -/
public theorem curve144_hasRankGE_9 : HasRankGE curve144 9 := by
  unfold curve144
  certify_curve torsion 7 "data/curve144.txt" "data/curve144-labels.txt"

/-- Curve 144 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve144.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 144. -/
public theorem curve144_j : curve144.j = 75467592338172369664 / 4704057937009713 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
