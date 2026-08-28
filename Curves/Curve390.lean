/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 390 has rank at least 26

The elliptic curve recorded as
[curve 390](https://elliptic-rank.icarm.cloud/curve/390) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -3430010766159976165957759077669961926755875`   and
  `a₆ = 2681763916740340149774032713047940546291901244757804845784121650`

over `ℚ`. It has Mordell-Weil rank at least `26`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve390.txt`; descent labels are in
`data/curve390-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 390 over `ℚ`. -/
@[expose] public def curve390 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -3430010766159976165957759077669961926755875,
    2681763916740340149774032713047940546291901244757804845784121650⟩

/-- ICARM leaderboard curve 390 has Mordell-Weil rank at least `26`. -/
public theorem curve390_hasRankGE_26 : HasRankGE curve390 26 := by
  unfold curve390
  certify_curve torsion 61 "data/curve390.txt" "data/curve390-labels.txt"

/-- Curve 390 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve390.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 390. -/
public theorem curve390_j : curve390.j = -6973168951799290597889281878092715639625360258604926605790789876243392538674005405140612660835388030571435586514416330115262500 / 819105252005157987426073609354356821548398756932808642346391088409214599151289825230467244309836851789948298400323981180583 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
