/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 383 has rank at least 18

The elliptic curve recorded as
[curve 383](https://elliptic-rank.icarm.cloud/curve/383) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -202780642049313963986778660430`   and
  `a₆ = 34519698985201688159263901059751374440368900`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve383.txt`; descent labels are in
`data/curve383-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 383 over `ℚ`. -/
@[expose] public def curve383 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -202780642049313963986778660430, 34519698985201688159263901059751374440368900⟩

/-- ICARM leaderboard curve 383 has Mordell-Weil rank at least `18`. -/
public theorem curve383_hasRankGE_18 : HasRankGE curve383 18 := by
  unfold curve383
  certify_curve torsion 7 "data/curve383.txt" "data/curve383-labels.txt"

/-- Curve 383 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve383.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 383. -/
public theorem curve383_j : curve383.j = 922153446002037117526942305269707820483345409432090321007859496786674870076135023069238474721 / 18878259596012030370825791301508298938819182134584892984497388982367104183322924800000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
