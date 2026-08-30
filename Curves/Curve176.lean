/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 176 has rank at least 16

The elliptic curve recorded as
[curve 176](https://elliptic-rank.icarm.cloud/curve/176) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -39457403617444107354653`   and
  `a₆ = 2995236809415759824391532391142437`

over `ℚ`. It has Mordell-Weil rank at least `16`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 176 over `ℚ`. -/
@[expose] public def curve176 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -39457403617444107354653, 2995236809415759824391532391142437⟩

/-- ICARM leaderboard curve 176 has Mordell-Weil rank at least `16`. -/
public theorem curve176_hasRankGE_16 : HasRankGE curve176 16 := by
  unfold curve176
  certify_curve torsion 7 "data/curve176.txt" "data/curve176-labels.txt"

/-- Curve 176 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve176.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 176. -/
public theorem curve176_j : curve176.j = 1896858489830426321635095174492419814689323279739907825163447575257 / 15608105462218022394741001041284679218977813496713703148748800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
