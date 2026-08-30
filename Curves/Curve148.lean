/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 148 has rank at least 15

The elliptic curve recorded as
[curve 148](https://elliptic-rank.icarm.cloud/curve/148) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -80634779807196097636`   and
  `a₆ = 278711474435456966031090976016`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 148 over `ℚ`. -/
@[expose] public def curve148 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -80634779807196097636, 278711474435456966031090976016⟩

/-- ICARM leaderboard curve 148 has Mordell-Weil rank at least `15`. -/
public theorem curve148_hasRankGE_15 : HasRankGE curve148 15 := by
  unfold curve148
  certify_curve torsion 13 "data/curve148.txt" "data/curve148-labels.txt"

/-- Curve 148 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve148.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 148. -/
public theorem curve148_j : curve148.j = -57981697410536619222769742919931073197689018830596894754388813889 / 3574107331245376801878879599917457045580677964135913881600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
