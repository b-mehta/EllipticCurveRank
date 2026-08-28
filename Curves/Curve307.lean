/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 307 has rank at least 15

The elliptic curve recorded as
[curve 307](https://elliptic-rank.icarm.cloud/curve/307) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1474705521041100338570986911092165596800135`   and
  `a₆ = 689016723668927095487122547447296652854367658972300541602585225`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve307.txt`; descent labels are in
`data/curve307-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 307 over `ℚ`. -/
@[expose] public def curve307 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1474705521041100338570986911092165596800135,
    689016723668927095487122547447296652854367658972300541602585225⟩

/-- ICARM leaderboard curve 307 has Mordell-Weil rank at least `15`. -/
public theorem curve307_hasRankGE_15 : HasRankGE curve307 15 := by
  unfold curve307
  certify_curve oneTorsion 2850484885610308264664 13 "data/curve307.txt" "data/curve307-labels.txt"

/-- Curve 307 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve307.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 307. -/
public theorem curve307_j : curve307.j = 103016973981049796758038556648885736881252729967523085996519902136252467617647615197462152623122961320511214962338729061829191 / 48384990698793103280278737937817823493812630615790725580973277039887251338499700433729843434071330192159129206128640000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
