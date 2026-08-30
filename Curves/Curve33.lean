/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 33 has rank at least 11

The elliptic curve recorded as
[curve 33](https://elliptic-rank.icarm.cloud/curve/33) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1033620669162578745`   and
  `a₆ = 404204621142300751511020144`

over `ℚ`. It has Mordell-Weil rank at least `11`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 33 over `ℚ`. -/
@[expose] public def curve33 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -1033620669162578745, 404204621142300751511020144⟩

/-- ICARM leaderboard curve 33 has Mordell-Weil rank at least `11`. -/
public theorem curve33_hasRankGE_11 : HasRankGE curve33 11 := by
  unfold curve33
  certify_curve oneTorsion 2397141952 5 "data/curve33.txt" "data/curve33-labels.txt"

/-- Curve 33 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve33.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 33. -/
public theorem curve33_j : curve33.j = 7632859798256949554486291882400956470013557401501161537536 / 5867082256750982134816246350141391912539926394682037 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
