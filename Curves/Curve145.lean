/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 145 has rank at least 11

The elliptic curve recorded as
[curve 145](https://elliptic-rank.icarm.cloud/curve/145) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -103672594`   and
  `a₆ = 405866860144`

over `ℚ`. It has Mordell-Weil rank at least `11`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve145.txt`; descent labels are in
`data/curve145-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 145 over `ℚ`. -/
@[expose] public def curve145 : WeierstrassCurve ℚ := ⟨1, -1, 0, -103672594, 405866860144⟩

/-- ICARM leaderboard curve 145 has Mordell-Weil rank at least `11`. -/
public theorem curve145_hasRankGE_11 : HasRankGE curve145 11 := by
  unfold curve145
  certify_curve torsion 13 "data/curve145.txt" "data/curve145-labels.txt"

/-- Curve 145 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve145.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 145. -/
public theorem curve145_j : curve145.j = 123229762096009753855985152761 / 160151805186732113986612 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
