/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 227 has rank at least 17

The elliptic curve recorded as
[curve 227](https://elliptic-rank.icarm.cloud/curve/227) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -3093247876694187640816`   and
  `a₆ = 62533675385974785566766181200209`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve227.txt`; descent labels are in
`data/curve227-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 227 over `ℚ`. -/
@[expose] public def curve227 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -3093247876694187640816, 62533675385974785566766181200209⟩

/-- ICARM leaderboard curve 227 has Mordell-Weil rank at least `17`. -/
public theorem curve227_hasRankGE_17 : HasRankGE curve227 17 := by
  unfold curve227
  certify_curve torsion 59 "data/curve227.txt" "data/curve227-labels.txt"

/-- Curve 227 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve227.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 227. -/
public theorem curve227_j : curve227.j = 3273164879169489275406512821242520515374126854376415826639130203223809 / 204873677594335180956576449314454322564972911516245035826771353600 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
