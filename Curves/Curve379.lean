/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 379 has rank at least 16

The elliptic curve recorded as
[curve 379](https://elliptic-rank.icarm.cloud/curve/379) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -65188168432120629806876619656`   and
  `a₆ = 6168701434404225366706167935131419820676100`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve379.txt`; descent labels are in
`data/curve379-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 379 over `ℚ`. -/
@[expose] public def curve379 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -65188168432120629806876619656, 6168701434404225366706167935131419820676100⟩

/-- ICARM leaderboard curve 379 has Mordell-Weil rank at least `16`. -/
public theorem curve379_hasRankGE_16 : HasRankGE curve379 16 := by
  unfold curve379
  certify_curve torsion 17 "data/curve379.txt" "data/curve379-labels.txt"

/-- Curve 379 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve379.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 379. -/
public theorem curve379_j : curve379.j = 29917830165262339974275857519821340045938342062904101279722074730588306772907943801868836 / 1260001475850590030964806565592013031584782304198029691672084841107053586742197493825 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
