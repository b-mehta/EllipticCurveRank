/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 339 has rank at least 19

The elliptic curve recorded as
[curve 339](https://elliptic-rank.icarm.cloud/curve/339) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -491829755436006895005968707827`   and
  `a₆ = 132444599116949764711601499902718391049688249`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve339.txt`; descent labels are in
`data/curve339-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 339 over `ℚ`. -/
@[expose] public def curve339 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -491829755436006895005968707827, 132444599116949764711601499902718391049688249⟩

/-- ICARM leaderboard curve 339 has Mordell-Weil rank at least `19`. -/
public theorem curve339_hasRankGE_19 : HasRankGE curve339 19 := by
  unfold curve339
  certify_curve torsion 47 "data/curve339.txt" "data/curve339-labels.txt"

/-- Curve 339 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve339.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 339. -/
public theorem curve339_j : curve339.j = 13157340423841835203191608351799353411197645615868037348444296294157527261366038509208715730361 / 36242601339908124690239703627094837632163784603962972713449076762616483455697692209362500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
