/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 291 has rank at least 19

The elliptic curve recorded as
[curve 291](https://elliptic-rank.icarm.cloud/curve/291) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -32356893962437167577665120678966`   and
  `a₆ = 70815900914955776688514954298475586029129608100`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 291 over `ℚ`. -/
@[expose] public def curve291 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -32356893962437167577665120678966, 70815900914955776688514954298475586029129608100⟩

/-- ICARM leaderboard curve 291 has Mordell-Weil rank at least `19`. -/
public theorem curve291_hasRankGE_19 : HasRankGE curve291 19 := by
  unfold curve291
  certify_curve torsion 17 "data/curve291.txt" "data/curve291-labels.txt"

/-- Curve 291 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve291.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 291. -/
public theorem curve291_j : curve291.j = 31844611072083867626865275224217865135441994937911558417029003592489253273460911238616408140241 / 14215435830148235529799662352264068087312446526429440014425522664485131428771957496217600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
