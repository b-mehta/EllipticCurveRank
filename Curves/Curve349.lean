/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 349 has rank at least 10

The elliptic curve recorded as
[curve 349](https://elliptic-rank.icarm.cloud/curve/349) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -60329721215`   and
  `a₆ = 5941090228603161`

over `ℚ`. It has Mordell-Weil rank at least `10`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 349 over `ℚ`. -/
@[expose] public def curve349 : WeierstrassCurve ℚ := ⟨1, 0, 0, -60329721215, 5941090228603161⟩

/-- ICARM leaderboard curve 349 has Mordell-Weil rank at least `10`. -/
public theorem curve349_hasRankGE_10 : HasRankGE curve349 10 := by
  unfold curve349
  certify_curve torsion 7 "data/curve349.txt" "data/curve349-labels.txt"

/-- Curve 349 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve349.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 349. -/
public theorem curve349_j : curve349.j = -24283857036447918798044044804481090161 / 1194978740460611711453288201945088 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
