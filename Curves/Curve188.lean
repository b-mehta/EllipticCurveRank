/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 188 has rank at least 16

The elliptic curve recorded as
[curve 188](https://elliptic-rank.icarm.cloud/curve/188) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -50180143404585230743736520`   and
  `a₆ = 138805605621811599445299434551151234112`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve188.txt`; descent labels are in
`data/curve188-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 188 over `ℚ`. -/
@[expose] public def curve188 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -50180143404585230743736520, 138805605621811599445299434551151234112⟩

/-- ICARM leaderboard curve 188 has Mordell-Weil rank at least `16`. -/
public theorem curve188_hasRankGE_16 : HasRankGE curve188 16 := by
  unfold curve188
  certify_curve torsion 13 "data/curve188.txt" "data/curve188-labels.txt"

/-- Curve 188 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve188.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 188. -/
public theorem curve188_j : curve188.j = -13973957125883220562037651650343965585513755782631433886665571960057418015894679681 / 236561593535490259936412512778599347267021742231315444284836282901094195200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
