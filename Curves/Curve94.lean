/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 94 has rank at least 18

The elliptic curve recorded as
[curve 94](https://elliptic-rank.icarm.cloud/curve/94) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -52751556365588628145400492670`   and
  `a₆ = 4655848829189654008696988351827664455270212`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve94.txt`; descent labels are in
`data/curve94-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 94 over `ℚ`. -/
@[expose] public def curve94 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -52751556365588628145400492670, 4655848829189654008696988351827664455270212⟩

/-- ICARM leaderboard curve 94 has Mordell-Weil rank at least `18`. -/
public theorem curve94_hasRankGE_18 : HasRankGE curve94 18 := by
  unfold curve94
  certify_curve torsion 41 "data/curve94.txt" "data/curve94-labels.txt"

/-- Curve 94 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve94.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 94. -/
public theorem curve94_j : curve94.j = 16234149627581448753576568183446697100352967616369047022072123486430843964358043838175597281 / 30329481606266546964270732939527654191747398716945306980836010472365688288267827200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
