/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 184 has rank at least 16

The elliptic curve recorded as
[curve 184](https://elliptic-rank.icarm.cloud/curve/184) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1169167431674669428559431663`   and
  `a₆ = 15401506519118600679103992536133903673781`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve184.txt`; descent labels are in
`data/curve184-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 184 over `ℚ`. -/
@[expose] public def curve184 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1169167431674669428559431663, 15401506519118600679103992536133903673781⟩

/-- ICARM leaderboard curve 184 has Mordell-Weil rank at least `16`. -/
public theorem curve184_hasRankGE_16 : HasRankGE curve184 16 := by
  unfold curve184
  certify_curve torsion 13 "data/curve184.txt" "data/curve184-labels.txt"

/-- Curve 184 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve184.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 184. -/
public theorem curve184_j : curve184.j = -11311854584048201117803592121398188161227202433482971814820309440525795815099753257 / 12070488214103983520646263384962617740746479771598131042342580349525194899456 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
