/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 453 has rank at least 20

The elliptic curve recorded as
[curve 453](https://elliptic-rank.icarm.cloud/curve/453) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -947722297710433437416491166575338`   and
  `a₆ = 10741271823987029219560000495736411788978103849892`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 453 over `ℚ`. -/
@[expose] public def curve453 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -947722297710433437416491166575338, 10741271823987029219560000495736411788978103849892⟩

/-- ICARM leaderboard curve 453 has Mordell-Weil rank at least `20`. -/
public theorem curve453_hasRankGE_20 : HasRankGE curve453 20 := by
  unfold curve453
  certify_curve torsion 17 "data/curve453.txt" "data/curve453-labels.txt"

/-- Curve 453 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve453.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 453. -/
public theorem curve453_j : curve453.j = 1894443354871745788956481914140566795562202661453459362687926839925355539731068930138911946517675 / 93300960320224647725231807596137333252692157715838351871832967116924893011300833995000152064 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
