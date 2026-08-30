/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 205 has rank at least 13

The elliptic curve recorded as
[curve 205](https://elliptic-rank.icarm.cloud/curve/205) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -18031282130466232369801290576`   and
  `a₆ = 937912694842853350198553539190914682552740`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 205 over `ℚ`. -/
@[expose] public def curve205 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -18031282130466232369801290576, 937912694842853350198553539190914682552740⟩

/-- ICARM leaderboard curve 205 has Mordell-Weil rank at least `13`. -/
public theorem curve205_hasRankGE_13 : HasRankGE curve205 13 := by
  unfold curve205
  certify_curve torsion 7 "data/curve205.txt" "data/curve205-labels.txt"

/-- Curve 205 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve205.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 205. -/
public theorem curve205_j : curve205.j = -128871480411962973459918638542369651526670377341462228301748036310485143871711035012 / 958966033340847435693437307012100399015394930580958465273641310764388555386275 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
