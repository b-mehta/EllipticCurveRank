/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 398 has rank at least 30

The elliptic curve recorded as
[curve 398](https://elliptic-rank.icarm.cloud/curve/398) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -12892599774455576272301592959047823530919513428112484011550`   and
  `a₆ = 5607550463483954129770888249995038906175588566876369812239356628483864849803`
  `     12656296132`

over `ℚ`. It has Mordell-Weil rank at least `30`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve398.txt`; descent labels are in
`data/curve398-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 398 over `ℚ`. -/
@[expose] public def curve398 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -12892599774455576272301592959047823530919513428112484011550,
    560755046348395412977088824999503890617558856687636981223935662848386484980312656296132⟩

/-- ICARM leaderboard curve 398 has Mordell-Weil rank at least `30`. -/
public theorem curve398_hasRankGE_30 : HasRankGE curve398 30 := by
  unfold curve398
  certify_curve torsion 23 "data/curve398.txt" "data/curve398-labels.txt"

/-- Curve 398 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve398.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 398. -/
public theorem curve398_j : curve398.j = 236998291526079648583854965652285717850317537544307333968062927596445176435890133930538298226374627836611773616054545227882944946054156107450589690022916396776998067961033759743201 / 1311021171349839305076869751181166178696551783990116503463598327754948038424504439658681699321482006153838737418363257993512584919966486940354703657840019569754443427840000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
