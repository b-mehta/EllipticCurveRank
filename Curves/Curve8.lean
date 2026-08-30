/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 8 has rank at least 22

The elliptic curve recorded as
[curve 8](https://elliptic-rank.icarm.cloud/curve/8) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -940299517776391362903023121165864`   and
  `a₆ = 10707363070719743033425295515449274534651125011362`

over `ℚ`. It has Mordell-Weil rank at least `22`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 8, Fermigier's rank-22 curve over `ℚ`. -/
@[expose] public def curve8 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -940299517776391362903023121165864, 10707363070719743033425295515449274534651125011362⟩

/-- ICARM leaderboard curve 8 has Mordell-Weil rank at least `22`. -/
public theorem curve8_hasRankGE_22 : HasRankGE curve8 22 := by
  unfold curve8
  certify_curve torsion 31 "data/curve8.txt" "data/curve8-labels.txt"

/-- Curve 8 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve8.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 8. -/
public theorem curve8_j : curve8.j = 1100846248533672637272667609024070259013561465803715126324232203980796387075272060111742614514870969 / 44065949951997237875354386996900989074346376691085288438660994521200484270128170183095654684900 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
