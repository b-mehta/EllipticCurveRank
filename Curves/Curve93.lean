/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 93 has rank at least 16

The elliptic curve recorded as
[curve 93](https://elliptic-rank.icarm.cloud/curve/93) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2888333461706975177036`   and
  `a₆ = 69181091953326695958744591394960`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve93.txt`; descent labels are in
`data/curve93-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 93 over `ℚ`. -/
@[expose] public def curve93 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2888333461706975177036, 69181091953326695958744591394960⟩

/-- ICARM leaderboard curve 93 has Mordell-Weil rank at least `16`. -/
public theorem curve93_hasRankGE_16 : HasRankGE curve93 16 := by
  unfold curve93
  certify_curve torsion 17 "data/curve93.txt" "data/curve93-labels.txt"

/-- Curve 93 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve93.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 93. -/
public theorem curve93_j : curve93.j = -2664806671860579550554013524751491656464084735663187087622793432951489 / 525428654379535377518565414066223922787670130763896329790210867200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
