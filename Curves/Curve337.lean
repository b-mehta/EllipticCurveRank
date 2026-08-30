/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 337 has rank at least 19

The elliptic curve recorded as
[curve 337](https://elliptic-rank.icarm.cloud/curve/337) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -162268279768512229548027479226276`   and
  `a₆ = 417944668872887979025847241579270199663848529680`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 337 over `ℚ`. -/
@[expose] public def curve337 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -162268279768512229548027479226276, 417944668872887979025847241579270199663848529680⟩

/-- ICARM leaderboard curve 337 has Mordell-Weil rank at least `19`. -/
public theorem curve337_hasRankGE_19 : HasRankGE curve337 19 := by
  unfold curve337
  certify_curve torsion 79 "data/curve337.txt" "data/curve337-labels.txt"

/-- Curve 337 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve337.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 337. -/
public theorem curve337_j : curve337.j = 555349158179604610508339626263519555456763270946686349093119341167993870973719760603751381999 / 232695028279417510285511346045636730895770330550311487009211639649911770985806046535065600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
