/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 429 has rank at least 20

The elliptic curve recorded as
[curve 429](https://elliptic-rank.icarm.cloud/curve/429) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3548379898700520547221772345212`   and
  `a₆ = 2596244984555180683994653333342076110656596799`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 429 over `ℚ`. -/
@[expose] public def curve429 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -3548379898700520547221772345212, 2596244984555180683994653333342076110656596799⟩

/-- ICARM leaderboard curve 429 has Mordell-Weil rank at least `20`. -/
public theorem curve429_hasRankGE_20 : HasRankGE curve429 20 := by
  unfold curve429
  certify_curve torsion 47 "data/curve429.txt" "data/curve429-labels.txt"

/-- Curve 429 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve429.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 429. -/
public theorem curve429_j : curve429.j = -4940990775988327059557188113000746050749005912841832247415933010930505706383582210287344965083281 / 52521162535382074717439043300866350950112927203157501676552632309040698338202829093120000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
