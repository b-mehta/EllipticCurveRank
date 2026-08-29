/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 182 has rank at least 16

The elliptic curve recorded as
[curve 182](https://elliptic-rank.icarm.cloud/curve/182) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -705592481967814336771305934410`   and
  `a₆ = 228068530382732810578825694652792716443320100`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve182.txt`; descent labels are in
`data/curve182-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 182 over `ℚ`. -/
@[expose] public def curve182 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -705592481967814336771305934410, 228068530382732810578825694652792716443320100⟩

/-- ICARM leaderboard curve 182 has Mordell-Weil rank at least `16`. -/
public theorem curve182_hasRankGE_16 : HasRankGE curve182 16 := by
  unfold curve182
  certify_curve torsion 41 "data/curve182.txt" "data/curve182-labels.txt"

/-- Curve 182 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve182.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 182. -/
public theorem curve182_j : curve182.j = 22755263298211147050614629743335994244908870787830527823740834254506254026979962711 / 6891333361529069721122348011626735824121621862097154739035016601600000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
