/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 322 has rank at least 19

The elliptic curve recorded as
[curve 322](https://elliptic-rank.icarm.cloud/curve/322) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -866215048931314001543961797`   and
  `a₆ = 8949093843799245559606590167545608201021`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 322 over `ℚ`. -/
@[expose] public def curve322 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -866215048931314001543961797, 8949093843799245559606590167545608201021⟩

/-- ICARM leaderboard curve 322 has Mordell-Weil rank at least `19`. -/
public theorem curve322_hasRankGE_19 : HasRankGE curve322 19 := by
  unfold curve322
  certify_curve torsion 17 "data/curve322.txt" "data/curve322-labels.txt"

/-- Curve 322 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve322.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 322. -/
public theorem curve322_j : curve322.j = 98599192328140736370356464797657623429162235639359538375197697889730160289926826249 / 9601181115750078873408882514666060846796833154512780600357817958099863923200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
