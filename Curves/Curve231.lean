/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 231 has rank at least 17

The elliptic curve recorded as
[curve 231](https://elliptic-rank.icarm.cloud/curve/231) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2356513159556540884992`   and
  `a₆ = 45035945457332407869731977363456`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve231.txt`; descent labels are in
`data/curve231-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 231 over `ℚ`. -/
@[expose] public def curve231 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2356513159556540884992, 45035945457332407869731977363456⟩

/-- ICARM leaderboard curve 231 has Mordell-Weil rank at least `17`. -/
public theorem curve231_hasRankGE_17 : HasRankGE curve231 17 := by
  unfold curve231
  certify_curve torsion 5 "data/curve231.txt" "data/curve231-labels.txt"

/-- Curve 231 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve231.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 231. -/
public theorem curve231_j : curve231.j = -1447215882896083294253687359981184440666730229223721988204117029978113 / 38688926074726301138649337130672103413740602433127643612028665856 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
