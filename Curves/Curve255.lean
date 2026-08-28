/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 255 has rank at least 7

The elliptic curve recorded as
[curve 255](https://elliptic-rank.icarm.cloud/curve/255) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 97151`   and
  `a₆ = 91204`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve255.txt`; descent labels are in
`data/curve255-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 255 over `ℚ`. -/
@[expose] public def curve255 : WeierstrassCurve ℚ := ⟨0, 0, 0, 97151, 91204⟩

/-- ICARM leaderboard curve 255 has Mordell-Weil rank at least `7`. -/
public theorem curve255_hasRankGE_7 : HasRankGE curve255 7 := by
  unfold curve255
  certify_curve torsion 5 "data/curve255.txt" "data/curve255-labels.txt"

/-- Curve 255 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve255.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 255. -/
public theorem curve255_j : curve255.j = 1584475630042667328 / 916998063178859 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
