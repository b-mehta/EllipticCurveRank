/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 431 has rank at least 20

The elliptic curve recorded as
[curve 431](https://elliptic-rank.icarm.cloud/curve/431) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -42135622063493348388166878576380`   and
  `a₆ = 105877466660516913227884540253347402151079039600`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 431 over `ℚ`. -/
@[expose] public def curve431 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -42135622063493348388166878576380, 105877466660516913227884540253347402151079039600⟩

/-- ICARM leaderboard curve 431 has Mordell-Weil rank at least `20`. -/
public theorem curve431_hasRankGE_20 : HasRankGE curve431 20 := by
  unfold curve431
  certify_curve torsion 23 "data/curve431.txt" "data/curve431-labels.txt"

/-- Curve 431 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve431.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 431. -/
public theorem curve431_j : curve431.j = -32317069830872023720911691450520226429453729760044906054020261658341292894142508845804725288803536 / 214931030655608377507355331040231968077533865390750103593864054188035690850890136781693371875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
