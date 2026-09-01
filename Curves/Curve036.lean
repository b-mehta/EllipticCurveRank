/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 36 has rank at least 15

The elliptic curve recorded as
[curve 36](https://elliptic-rank.icarm.cloud/curve/36) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = 34318214642441646362435632562579908747`   and
  `a₆ = 3184376895814127197244886284686214848599453811643486936756`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 36 over `ℚ`. -/
@[expose] public def curve036 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, 34318214642441646362435632562579908747,
    3184376895814127197244886284686214848599453811643486936756⟩

/-- ICARM leaderboard curve 36 has Mordell-Weil rank at least `15`. -/
public theorem curve036_hasRankGE_15 : HasRankGE curve036 15 := by
  unfold curve036
  certify_curve oneTorsion (-55741267008740887705) 19 "data/curve036.txt" "data/curve036-labels.txt"

/-- Curve 36 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve036.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 36. -/
public theorem curve036_j : curve036.j = 32531571958650407988772073099447997522262041696655381207016276651058371579669754953 / 31900414783853533899787571633007620668088840400343419021633930581913312084960937500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
