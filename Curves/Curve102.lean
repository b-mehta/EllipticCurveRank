/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 102 has rank at least 18

The elliptic curve recorded as
[curve 102](https://elliptic-rank.icarm.cloud/curve/102) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -354423968717233792815730830`   and
  `a₆ = 2561986646153119712343318111147387184797`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve102.txt`; descent labels are in
`data/curve102-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 102 over `ℚ`. -/
@[expose] public def curve102 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -354423968717233792815730830, 2561986646153119712343318111147387184797⟩

/-- ICARM leaderboard curve 102 has Mordell-Weil rank at least `18`. -/
public theorem curve102_hasRankGE_18 : HasRankGE curve102 18 := by
  unfold curve102
  certify_curve torsion 7 "data/curve102.txt" "data/curve102-labels.txt"

/-- Curve 102 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve102.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 102. -/
public theorem curve102_j : curve102.j = 315117802450922490346187827221773330564043350897366667372193541687008427584830057 / 884572281883493047744392135952959288852168027241749272493693107109609324544 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
