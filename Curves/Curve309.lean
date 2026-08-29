/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 309 has rank at least 15

The elliptic curve recorded as
[curve 309](https://elliptic-rank.icarm.cloud/curve/309) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -139247897426027149067804108174260263825601`   and
  `a₆ = -12171148262466750740691943470052015013728330466029726884498652`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve309.txt`; descent labels are in
`data/curve309-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 309 over `ℚ`. -/
@[expose] public def curve309 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -139247897426027149067804108174260263825601,
    -12171148262466750740691943470052015013728330466029726884498652⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 309 has Mordell-Weil rank at least `15`. -/
public theorem curve309_hasRankGE_15 : HasRankGE curve309 15 := by
  unfold curve309
  certify_curve oneTorsion (-1270834299719617671092) 11 "data/curve309.txt" "data/curve309-labels.txt"

/-- Curve 309 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve309.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 309. -/
public theorem curve309_j : curve309.j = 263568014249955867908411449834130573082707805594166141467699766335406025854896858906880630766476054612296740723 / 96040604464192185833139530876194607248000231347169965046835104741513840485519564553091674600150090237229616 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
