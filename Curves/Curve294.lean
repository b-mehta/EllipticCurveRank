/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 294 has rank at least 19

The elliptic curve recorded as
[curve 294](https://elliptic-rank.icarm.cloud/curve/294) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -4101421576978444120802996800`   and
  `a₆ = 101007831382914631822039670440279140956948`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve294.txt`; descent labels are in
`data/curve294-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 294 over `ℚ`. -/
@[expose] public def curve294 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -4101421576978444120802996800, 101007831382914631822039670440279140956948⟩

/-- ICARM leaderboard curve 294 has Mordell-Weil rank at least `19`. -/
public theorem curve294_hasRankGE_19 : HasRankGE curve294 19 := by
  unfold curve294
  certify_curve torsion 17 "data/curve294.txt" "data/curve294-labels.txt"

/-- Curve 294 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve294.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 294. -/
public theorem curve294_j : curve294.j = 3725606609283602221301131031470119687617868729802723226506190581457155609528734902402 / 3915202567066901197776311550550772976949411425431401627039958502267910513959375 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
