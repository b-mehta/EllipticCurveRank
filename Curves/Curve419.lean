/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 419 has rank at least 20

The elliptic curve recorded as
[curve 419](https://elliptic-rank.icarm.cloud/curve/419) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -24403746364851709763421313327110`   and
  `a₆ = 46771399861468337270143023679331346542490944100`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 419 over `ℚ`. -/
@[expose] public def curve419 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -24403746364851709763421313327110, 46771399861468337270143023679331346542490944100⟩

/-- ICARM leaderboard curve 419 has Mordell-Weil rank at least `20`. -/
public theorem curve419_hasRankGE_20 : HasRankGE curve419 20 := by
  unfold curve419
  certify_curve torsion 19 "data/curve419.txt" "data/curve419-labels.txt"

/-- Curve 419 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve419.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 419. -/
public theorem curve419_j : curve419.j = -1607286214814573498465050827746731831767477938271714328724905515283476789532704137035164219557171041 / 14885095615487370251227862371409868728570596128315061788060679120737629177954766051012864000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
