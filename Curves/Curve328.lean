/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 328 has rank at least 20

The elliptic curve recorded as
[curve 328](https://elliptic-rank.icarm.cloud/curve/328) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -173863764473375398357582442830175`   and
  `a₆ = 883145447815390783031613032285356595588099614085`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve328.txt`; descent labels are in
`data/curve328-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 328 over `ℚ`. -/
@[expose] public def curve328 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -173863764473375398357582442830175, 883145447815390783031613032285356595588099614085⟩

/-- ICARM leaderboard curve 328 has Mordell-Weil rank at least `20`. -/
public theorem curve328_hasRankGE_20 : HasRankGE curve328 20 := by
  unfold curve328
  certify_curve torsion 7 "data/curve328.txt" "data/curve328-labels.txt"

/-- Curve 328 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve328.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 328. -/
public theorem curve328_j : curve328.j = -581233915932309009911811668849497787289778814720893969975161739004278009856669913271220661807019225201 / 574401154490032448091180309990921523509969094823336020555771703114693561881267196456934604800000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
