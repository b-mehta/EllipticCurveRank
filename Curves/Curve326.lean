/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 326 has rank at least 10

The elliptic curve recorded as
[curve 326](https://elliptic-rank.icarm.cloud/curve/326) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -399667220820`   and
  `a₆ = 32642129216035332`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve326.txt`; descent labels are in
`data/curve326-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 326 over `ℚ`. -/
@[expose] public def curve326 : WeierstrassCurve ℚ := ⟨0, -1, 0, -399667220820, 32642129216035332⟩

/-- ICARM leaderboard curve 326 has Mordell-Weil rank at least `10`. -/
public theorem curve326_hasRankGE_10 : HasRankGE curve326 10 := by
  unfold curve326
  certify_curve torsion 11 "data/curve326.txt" "data/curve326-labels.txt"

/-- Curve 326 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve326.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 326. -/
public theorem curve326_j : curve326.j = 27579052302027671871046668930874850896 / 14162068626440481637527957055115625 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
