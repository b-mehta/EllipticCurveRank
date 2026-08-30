/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 226 has rank at least 20

The elliptic curve recorded as
[curve 226](https://elliptic-rank.icarm.cloud/curve/226) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -53324817965388276805370879748910`   and
  `a₆ = 152600569230942786227963554343099291511940660100`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 226 over `ℚ`. -/
@[expose] public def curve226 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -53324817965388276805370879748910, 152600569230942786227963554343099291511940660100⟩

/-- ICARM leaderboard curve 226 has Mordell-Weil rank at least `20`. -/
public theorem curve226_hasRankGE_20 : HasRankGE curve226 20 := by
  unfold curve226
  certify_curve torsion 43 "data/curve226.txt" "data/curve226-labels.txt"

/-- Curve 226 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve226.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 226. -/
public theorem curve226_j : curve226.j = -16769181173589727873782247531970437045601133482103485398023188599776346363946448714530690742888822241 / 355568117955757642974912655755100242442938536081550074372306129807997878195940027796106400000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
