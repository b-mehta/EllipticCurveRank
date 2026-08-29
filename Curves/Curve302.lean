/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 302 has rank at least 31

The elliptic curve recorded as
[curve 302](https://elliptic-rank.icarm.cloud/curve/302) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1284727764113567728281797636015784768866707681415849262157224232063`   and
  `a₆ = 5603683214542613392568593389019153123327698586849454068580438691994567106819`
  `     89058863306170127006181`

over `ℚ`. It has Mordell-Weil rank at least `31`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve302.txt`; descent labels are in
`data/curve302-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 302 over `ℚ`. -/
@[expose] public def curve302 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1284727764113567728281797636015784768866707681415849262157224232063,
    560368321454261339256859338901915312332769858684945406858043869199456710681989058863306170127006181⟩

/-- ICARM leaderboard curve 302 has Mordell-Weil rank at least `31`. -/
public theorem curve302_hasRankGE_31 : HasRankGE curve302 31 := by
  unfold curve302
  certify_curve torsion 31 "data/curve302.txt" "data/curve302-labels.txt"

/-- Curve 302 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve302.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 302. -/
public theorem curve302_j : curve302.j = 375212263011874190418465904591842149883143397000379116040077721209939307800933802063374036449207052554068812677819360841029222896769044613030052189320099029335648176287279769780720048237450063678337025 / 91178667460631761509802129711614912708907877152843688131591561513957139867216918982080782638846592571825918112525868294328087917747020295905203091292094298537560118649108877196489360560362979328 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
