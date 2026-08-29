/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 229 has rank at least 17

The elliptic curve recorded as
[curve 229](https://elliptic-rank.icarm.cloud/curve/229) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -202989927789473297517`   and
  `a₆ = 1151371062064532719495377812641`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve229.txt`; descent labels are in
`data/curve229-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 229 over `ℚ`. -/
@[expose] public def curve229 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -202989927789473297517, 1151371062064532719495377812641⟩

/-- ICARM leaderboard curve 229 has Mordell-Weil rank at least `17`. -/
public theorem curve229_hasRankGE_17 : HasRankGE curve229 17 := by
  unfold curve229
  certify_curve torsion 7 "data/curve229.txt" "data/curve229-labels.txt"

/-- Curve 229 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve229.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 229. -/
public theorem curve229_j : curve229.j = -81208151508020667086660223535998619051907804858109460361353 / 3281247513650178094476447106893655211025350682159534924 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
