/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 319 has rank at least 15

The elliptic curve recorded as
[curve 319](https://elliptic-rank.icarm.cloud/curve/319) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1478818379630960182018543975144238479079598870400357903794`   and
  `a₆ = 2161233337156436290622782006484637668522738000673236838885121727607651856378`
  `     6908263808`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve319.txt`; descent labels are in
`data/curve319-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 319 over `ℚ`. -/
@[expose] public def curve319 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -1478818379630960182018543975144238479079598870400357903794,
    21612333371564362906227820064846376685227380006732368388851217276076518563786908263808⟩

/-- ICARM leaderboard curve 319 has Mordell-Weil rank at least `15`. -/
public theorem curve319_hasRankGE_15 : HasRankGE curve319 15 := by
  unfold curve319
  certify_curve fullTorsion "data/curve319.txt" "data/curve319-labels.txt"

/-- Curve 319 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve319.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 319. -/
public theorem curve319_j : curve319.j = 490614864983637444980599597597366271704351393611962066437403646683927890768991284963186046452338087155635780945486661043407781706521170056163833479553130759149924704439519009 / 7124815005599300846995063954137472444849463822640144341907655280683803106878375006962073031776264959458411324959684073365160240967552433646149103254236895341595351562500 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
