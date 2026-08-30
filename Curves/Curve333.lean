/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 333 has rank at least 19

The elliptic curve recorded as
[curve 333](https://elliptic-rank.icarm.cloud/curve/333) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -23891105188685143592112789788`   and
  `a₆ = 1419601215093448810627501450420291027410192`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 333 over `ℚ`. -/
@[expose] public def curve333 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -23891105188685143592112789788, 1419601215093448810627501450420291027410192⟩

/-- ICARM leaderboard curve 333 has Mordell-Weil rank at least `19`. -/
public theorem curve333_hasRankGE_19 : HasRankGE curve333 19 := by
  unfold curve333
  certify_curve torsion 43 "data/curve333.txt" "data/curve333-labels.txt"

/-- Curve 333 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve333.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 333. -/
public theorem curve333_j : curve333.j = 96518909703233033434163617276493273887941846775696513023061140661309602612570057630457 / 137731644332816948398017774920067097767253737948852991745512420846250430440914944 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
