/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 345 has rank at least 19

The elliptic curve recorded as
[curve 345](https://elliptic-rank.icarm.cloud/curve/345) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -484958388528014875755905011`   and
  `a₆ = 3744479970311738957262814782831867617210`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by Christopher R.
Hill.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 345 over `ℚ`. -/
@[expose] public def curve345 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -484958388528014875755905011, 3744479970311738957262814782831867617210⟩

/-- ICARM leaderboard curve 345 has Mordell-Weil rank at least `19`. -/
public theorem curve345_hasRankGE_19 : HasRankGE curve345 19 := by
  unfold curve345
  certify_curve torsion 37 "data/curve345.txt" "data/curve345-labels.txt"

/-- Curve 345 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve345.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 345. -/
public theorem curve345_j : curve345.j = 2567381312378641934111041928290166475319811411825816551509053899686223977916903553 / 252875348430269250279547286234207310670836340483994640182484967790285287913775 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
