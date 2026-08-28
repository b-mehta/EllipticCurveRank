/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 286 has rank at least 21

The elliptic curve recorded as
[curve 286](https://elliptic-rank.icarm.cloud/curve/286) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -11525691028496208487693310738282`   and
  `a₆ = 18833323594165105316445398903949581636278347689`

over `ℚ`. It has Mordell-Weil rank at least `21`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve286.txt`; descent labels are in
`data/curve286-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 286 over `ℚ`. -/
@[expose] public def curve286 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -11525691028496208487693310738282, 18833323594165105316445398903949581636278347689⟩

/-- ICARM leaderboard curve 286 has Mordell-Weil rank at least `21`. -/
public theorem curve286_hasRankGE_21 : HasRankGE curve286 21 := by
  unfold curve286
  certify_curve torsion 13 "data/curve286.txt" "data/curve286-labels.txt"

/-- Curve 286 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve286.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 286. -/
public theorem curve286_j : curve286.j = -232272130428973862327781554052424230174468214598189351411062430190918055281921982903633639358809 / 75772340877328085674921853422124938783046156016372736772652112104648411927352528137600000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
