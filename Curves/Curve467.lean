/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 467 has rank at least 17

The elliptic curve recorded as
[curve 467](https://elliptic-rank.icarm.cloud/curve/467) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1375414938269729933430`   and
  `a₆ = 20780863582673042643051322404516`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Rayan Hatout.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 467 over `ℚ`. -/
@[expose] public def curve467 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1375414938269729933430, 20780863582673042643051322404516⟩

/-- ICARM leaderboard curve 467 has Mordell-Weil rank at least `17`. -/
public theorem curve467_hasRankGE_17 : HasRankGE curve467 17 := by
  unfold curve467
  certify_curve torsion 7 "data/curve467.txt" "data/curve467-labels.txt"

/-- Curve 467 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve467.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 467. -/
public theorem curve467_j : curve467.j = -19654146191586651330314323954101308540216082201889944209441528881 / 1368148744491431208123062041662972872155234342090499291086848 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
