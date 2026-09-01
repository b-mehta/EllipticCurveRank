/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 478 has rank at least 21

The elliptic curve recorded as
[curve 478](https://elliptic-rank.icarm.cloud/curve/478) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -142439622805746929644754975203567774592`   and
  `a₆ = 564187004933212877252354468248101698569580185650481725859`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Alexandar Slavov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 478 over `ℚ`. -/
@[expose] public def curve478 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -142439622805746929644754975203567774592,
    564187004933212877252354468248101698569580185650481725859⟩

/-- ICARM leaderboard curve 478 has Mordell-Weil rank at least `21`. -/
public theorem curve478_hasRankGE_21 : HasRankGE curve478 21 := by
  unfold curve478
  certify_curve torsion 17 "data/curve478.txt" "data/curve478-labels.txt"

/-- Curve 478 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve478.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 478. -/
public theorem curve478_j : curve478.j = 182598190131155573738500972693767848930212899825039087960305138698690860721662588504811298859545056622796416596569 / 27108667716707337649173199722590366624842452900450689879226681130487784248194044016264323993770903277568000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
