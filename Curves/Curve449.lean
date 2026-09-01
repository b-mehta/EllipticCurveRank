/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 449 has rank at least 20

The elliptic curve recorded as
[curve 449](https://elliptic-rank.icarm.cloud/curve/449) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -45985559764874647626604299762930`   and
  `a₆ = 84640033039127748879277321178403309377568768900`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 449 over `ℚ`. -/
@[expose] public def curve449 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -45985559764874647626604299762930, 84640033039127748879277321178403309377568768900⟩

/-- ICARM leaderboard curve 449 has Mordell-Weil rank at least `20`. -/
public theorem curve449_hasRankGE_20 : HasRankGE curve449 20 := by
  unfold curve449
  certify_curve torsion 17 "data/curve449.txt" "data/curve449-labels.txt"

/-- Curve 449 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve449.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 449. -/
public theorem curve449_j : curve449.j = 10754448500023831603482665388403821037521476831650481542401703874748166097185654092196478849186034721 / 3128819174937008750747092070091173185332512185826818190669176860413746229895787257077955072000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
