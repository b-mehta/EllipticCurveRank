/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 88 has rank at least 12

The elliptic curve recorded as
[curve 88](https://elliptic-rank.icarm.cloud/curve/88) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -932733487`   and
  `a₆ = 11052354147250`

over `ℚ`. It has Mordell-Weil rank at least `12`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve88.txt`; descent labels are in
`data/curve88-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 88 over `ℚ`. -/
@[expose] public def curve88 : WeierstrassCurve ℚ := ⟨0, 0, 0, -932733487, 11052354147250⟩

/-- ICARM leaderboard curve 88 has Mordell-Weil rank at least `12`. -/
public theorem curve88_hasRankGE_12 : HasRankGE curve88 12 := by
  unfold curve88
  certify_curve torsion 7 "data/curve88.txt" "data/curve88-labels.txt"

/-- Curve 88 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve88.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 88. -/
public theorem curve88_j : curve88.j = -350555232623257999182153154896 / 3268161609352514926041143 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
