/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 434 has rank at least 20

The elliptic curve recorded as
[curve 434](https://elliptic-rank.icarm.cloud/curve/434) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -119748659652394027153495287863671115`   and
  `a₆ = 15870961531086086871587619570217861268496637395066225`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 434 over `ℚ`. -/
@[expose] public def curve434 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -119748659652394027153495287863671115,
    15870961531086086871587619570217861268496637395066225⟩

/-- ICARM leaderboard curve 434 has Mordell-Weil rank at least `20`. -/
public theorem curve434_hasRankGE_20 : HasRankGE curve434 20 := by
  unfold curve434
  certify_curve torsion 47 "data/curve434.txt" "data/curve434-labels.txt"

/-- Curve 434 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve434.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 434. -/
public theorem curve434_j : curve434.j = 79093999211529966080211981185972178407723134496990035370428208601509403325815957178643694698833450659153361 / 451138386922251618249937347328310413683596667688735687787186698363345798290816295726351807478016000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
