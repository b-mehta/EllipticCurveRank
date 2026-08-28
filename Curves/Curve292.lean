/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 292 has rank at least 19

The elliptic curve recorded as
[curve 292](https://elliptic-rank.icarm.cloud/curve/292) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -64638901051375115282329208`   and
  `a₆ = 199985543623639494018271452767098585212`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve292.txt`; descent labels are in
`data/curve292-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 292 over `ℚ`. -/
@[expose] public def curve292 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -64638901051375115282329208, 199985543623639494018271452767098585212⟩

/-- ICARM leaderboard curve 292 has Mordell-Weil rank at least `19`. -/
public theorem curve292_hasRankGE_19 : HasRankGE curve292 19 := by
  unfold curve292
  certify_curve torsion 7 "data/curve292.txt" "data/curve292-labels.txt"

/-- Curve 292 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve292.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 292. -/
public theorem curve292_j : curve292.j = 29867963012203309790573364900700040218558515649643069606963712488899677335595886729 / 7198788795422377711047836001349527968822437304655333414525981769447346162100 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
