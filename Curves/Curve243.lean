/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 243 has rank at least 20

The elliptic curve recorded as
[curve 243](https://elliptic-rank.icarm.cloud/curve/243) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -791198747812844165197303241658`   and
  `a₆ = 291678735985274857428612896086571996361540568`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve243.txt`; descent labels are in
`data/curve243-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 243 over `ℚ`. -/
@[expose] public def curve243 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -791198747812844165197303241658, 291678735985274857428612896086571996361540568⟩

/-- ICARM leaderboard curve 243 has Mordell-Weil rank at least `20`. -/
public theorem curve243_hasRankGE_20 : HasRankGE curve243 20 := by
  unfold curve243
  certify_curve torsion 13 "data/curve243.txt" "data/curve243-labels.txt"

/-- Curve 243 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve243.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 243. -/
public theorem curve243_j : curve243.j = -1838634497730906367035294092735792047747716300261156929164531658892387645469496289608179591 / 169671540513947824612760536641837110330894180865700264830211469042939923401160703062500 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
