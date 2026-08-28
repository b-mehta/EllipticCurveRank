/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 63 has rank at least 18

The elliptic curve recorded as
[curve 63](https://elliptic-rank.icarm.cloud/curve/63) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1718612993735110076283239582307203184558215`   and
  `a₆ = 445677626128337788660554947611110167094039534522619288819463817`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve63.txt`; descent labels are in
`data/curve63-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 63 over `ℚ`. -/
@[expose] public def curve63 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1718612993735110076283239582307203184558215,
    445677626128337788660554947611110167094039534522619288819463817⟩

/-- ICARM leaderboard curve 63 has Mordell-Weil rank at least `18`. -/
public theorem curve63_hasRankGE_18 : HasRankGE curve63 18 := by
  unfold curve63
  certify_curve oneTorsion (-5700969771220616529329) 29 "data/curve63.txt" "data/curve63-labels.txt"

/-- Curve 63 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve63.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 63. -/
public theorem curve63_j : curve63.j = 163052380316568670465839586154811939936483011279120507494354683890227424754907653927917028580543026879805411806135176570800711 / 69436346253531918496288527712013370970843517428551661770054029287060190609564655959840157952103526065125170525867600000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
