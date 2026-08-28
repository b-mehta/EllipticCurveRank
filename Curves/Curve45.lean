/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 45 has rank at least 13

The elliptic curve recorded as
[curve 45](https://elliptic-rank.icarm.cloud/curve/45) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -560715933702165990261993692150795879540`   and
  `a₆ = 5299428030171662962897867758309003693598430128674403539600`

over `ℚ`. It has Mordell-Weil rank at least `13`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve45.txt`; descent labels are in
`data/curve45-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 45 over `ℚ`. -/
@[expose] public def curve45 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -560715933702165990261993692150795879540,
    5299428030171662962897867758309003693598430128674403539600⟩

/-- ICARM leaderboard curve 45 has Mordell-Weil rank at least `13`. -/
public theorem curve45_hasRankGE_13 : HasRankGE curve45 13 := by
  unfold curve45
  certify_curve torsion 67 "data/curve45.txt" "data/curve45-labels.txt"

/-- Curve 45 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve45.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 45. -/
public theorem curve45_j : curve45.j = -19496309232463059890453494264411680808144164126541233061898434907023624909936853809079737916304194302096528144764939120961 / 849674615711570771215349016224804046891153693433134502714153993581965535857133434327195120355094716597801586176000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
