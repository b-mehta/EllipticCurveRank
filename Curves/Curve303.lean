/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 303 has rank at least 16

The elliptic curve recorded as
[curve 303](https://elliptic-rank.icarm.cloud/curve/303) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -14418406441122314356613`   and
  `a₆ = 574135768533729332199631492462717`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve303.txt`; descent labels are in
`data/curve303-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 303 over `ℚ`. -/
@[expose] public def curve303 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -14418406441122314356613, 574135768533729332199631492462717⟩

/-- ICARM leaderboard curve 303 has Mordell-Weil rank at least `16`. -/
public theorem curve303_hasRankGE_16 : HasRankGE curve303 16 := by
  unfold curve303
  certify_curve torsion 7 "data/curve303.txt" "data/curve303-labels.txt"

/-- Curve 303 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve303.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 303. -/
public theorem curve303_j : curve303.j = 454724103003105449756667754639389180830246456214597963637817403585801 / 67813111782692268344618349653923233568882794986451132841944678400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
