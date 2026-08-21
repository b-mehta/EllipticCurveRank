/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Soundness.JInvariant

/-!
# Curve 74 has rank at least 21

The elliptic curve recorded as
[curve 74](https://elliptic-rank.icarm.cloud/curve/74) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `                  - 19474361277787151947255961435459054151501792241320535`

over `ℚ`. It has Mordell-Weil rank at least `21`, the 1994 rank record of K. Nagao and T. Kouya.
Points in `data/curve74.txt`, descent labels in `data/curve74-labels.txt`; `certify_curve` does the
rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 74, the Nagao-Kouya rank-21 curve over `ℚ`. -/
def curve74 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -215843772422443922015169952702159835,
    -19474361277787151947255961435459054151501792241320535⟩

/-- ICARM leaderboard curve 74 has Mordell-Weil rank at least `21`. -/
theorem curve74_hasRankGE_21 : HasRankGE curve74 21 := by
  unfold curve74
  certify_curve torsion 11 "data/curve74.txt" "data/curve74-labels.txt"

/-- Curve 74 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve74.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 74. -/
theorem curve74_j : curve74.j = 1112096004752851462729397594359132384395809315460462776640080386721422130341804188923888915794608773116288507441 / 479737754043767746536923774462246533556793859277365678757052823009411494064048885744243744500948985175040000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
