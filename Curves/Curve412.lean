/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 412 has rank at least 21

The elliptic curve recorded as
[curve 412](https://elliptic-rank.icarm.cloud/curve/412) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -307611847416435887033706352943575`   and
  `a₆ = 2290502402472665291747329823139073039386938155625`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 412 over `ℚ`. -/
@[expose] public def curve412 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -307611847416435887033706352943575, 2290502402472665291747329823139073039386938155625⟩

/-- ICARM leaderboard curve 412 has Mordell-Weil rank at least `21`. -/
public theorem curve412_hasRankGE_21 : HasRankGE curve412 21 := by
  unfold curve412
  certify_curve torsion 47 "data/curve412.txt" "data/curve412-labels.txt"

/-- Curve 412 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve412.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 412. -/
public theorem curve412_j : curve412.j = -1340728143699069521186104398345186633109493738915783256411975294319318841231619139795228391309792401 / 168074567401081493068010852756830055901933195583019506443550790129640398485741328944487424000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
