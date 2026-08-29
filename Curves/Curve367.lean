/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 367 has rank at least 8

The elliptic curve recorded as
[curve 367](https://elliptic-rank.icarm.cloud/curve/367) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -52835555`   and
  `a₆ = 169776941347`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve367.txt`; descent labels are in
`data/curve367-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 367 over `ℚ`. -/
@[expose] public def curve367 : WeierstrassCurve ℚ := ⟨1, -1, 1, -52835555, 169776941347⟩

/-- ICARM leaderboard curve 367 has Mordell-Weil rank at least `8`. -/
public theorem curve367_hasRankGE_8 : HasRankGE curve367 8 := by
  unfold curve367
  certify_curve torsion 13 "data/curve367.txt" "data/curve367-labels.txt"

/-- Curve 367 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve367.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 367. -/
public theorem curve367_j : curve367.j = -35800985357045228165625 / 6607205932146556928 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
