/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 140 has rank at least 17

The elliptic curve recorded as
[curve 140](https://elliptic-rank.icarm.cloud/curve/140) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3594058853231188157738`   and
  `a₆ = 71746738560038807966948556541092`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve140.txt`; descent labels are in
`data/curve140-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 140 over `ℚ`. -/
@[expose] public def curve140 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3594058853231188157738, 71746738560038807966948556541092⟩

/-- ICARM leaderboard curve 140 has Mordell-Weil rank at least `17`. -/
public theorem curve140_hasRankGE_17 : HasRankGE curve140 17 := by
  unfold curve140
  certify_curve torsion 13 "data/curve140.txt" "data/curve140-labels.txt"

/-- Curve 140 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve140.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 140. -/
public theorem curve140_j : curve140.j = 328593705212759091728619447773313214590023848395477010103337336793 / 47837701648975701684345670558535998864936696868772679998790656 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
