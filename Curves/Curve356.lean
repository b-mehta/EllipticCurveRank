/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 356 has rank at least 29

The elliptic curve recorded as
[curve 356](https://elliptic-rank.icarm.cloud/curve/356) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -24391876744717707263532695900840552395172973498186560300`   and
  `a₆ = 4694390643378062045684483269905134043969871158874384520730955765627424178547`
  `     9710000`

over `ℚ`. It has Mordell-Weil rank at least `29`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve356.txt`; descent labels are in
`data/curve356-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 356 over `ℚ`. -/
@[expose] public def curve356 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -24391876744717707263532695900840552395172973498186560300,
    46943906433780620456844832699051340439698711588743845207309557656274241785479710000⟩

/-- ICARM leaderboard curve 356 has Mordell-Weil rank at least `29`. -/
public theorem curve356_hasRankGE_29 : HasRankGE curve356 29 := by
  unfold curve356
  certify_curve torsion 17 "data/curve356.txt" "data/curve356-labels.txt"

/-- Curve 356 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve356.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 356. -/
public theorem curve356_j : curve356.j = -6269304979845216954180474107964236883093366229250053435188280568027048697421724052240535825519946281433161245836403423888092120684546840521155592517406084571460519563216 / 90724956272739281140548641860939027287262202267374386853850123537496837825431026396331026124780490448645951855330227344308171529147373250905806946195368048088046875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
