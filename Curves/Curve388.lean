/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 388 has rank at least 19

The elliptic curve recorded as
[curve 388](https://elliptic-rank.icarm.cloud/curve/388) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -22712780660696177254170711756480`   and
  `a₆ = 41395746156416669814359661263389227736207101952`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve388.txt`; descent labels are in
`data/curve388-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 388 over `ℚ`. -/
@[expose] public def curve388 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -22712780660696177254170711756480, 41395746156416669814359661263389227736207101952⟩

/-- ICARM leaderboard curve 388 has Mordell-Weil rank at least `19`. -/
public theorem curve388_hasRankGE_19 : HasRankGE curve388 19 := by
  unfold curve388
  certify_curve torsion 17 "data/curve388.txt" "data/curve388-labels.txt"

/-- Curve 388 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve388.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 388. -/
public theorem curve388_j : curve388.j = 1295790026252322245731021387828529591838258488666403277450201225463168283251751306159322282303441921 / 9599917880856536381058881627733998505888507258688104953135739473953992158955863999360000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
