/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 420 has rank at least 20

The elliptic curve recorded as
[curve 420](https://elliptic-rank.icarm.cloud/curve/420) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -181942231909583197148101236805013`   and
  `a₆ = 997946339099553525501068395789161466011460824417`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 420 over `ℚ`. -/
@[expose] public def curve420 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -181942231909583197148101236805013, 997946339099553525501068395789161466011460824417⟩

/-- ICARM leaderboard curve 420 has Mordell-Weil rank at least `20`. -/
public theorem curve420_hasRankGE_20 : HasRankGE curve420 20 := by
  unfold curve420
  certify_curve torsion 29 "data/curve420.txt" "data/curve420-labels.txt"

/-- Curve 420 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve420.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 420. -/
public theorem curve420_j : curve420.j = -3808315361787059398520729151822847099688312245730877341967010750472847774730605527496337890625 / 255953255252560844188983698266683263049132353265862066973914120752903807081976025509527552 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
