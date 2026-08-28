/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 327 has rank at least 20

The elliptic curve recorded as
[curve 327](https://elliptic-rank.icarm.cloud/curve/327) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -262245552282515254065846883236370270`   and
  `a₆ = 44358788730180391915082790816530673754979831118248900`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve327.txt`; descent labels are in
`data/curve327-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 327 over `ℚ`. -/
@[expose] public def curve327 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -262245552282515254065846883236370270,
    44358788730180391915082790816530673754979831118248900⟩

/-- ICARM leaderboard curve 327 has Mordell-Weil rank at least `20`. -/
public theorem curve327_hasRankGE_20 : HasRankGE curve327 20 := by
  unfold curve327
  certify_curve torsion 29 "data/curve327.txt" "data/curve327-labels.txt"

/-- Curve 327 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve327.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 327. -/
public theorem curve327_j : curve327.j = 1994564595553088356862361351750687526193134467120690878519584591868639252412669269921760189760705369678869139681 / 304214595275859552600848995003180962782409909159288730912914252576839066152627207520825504275130200320000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
