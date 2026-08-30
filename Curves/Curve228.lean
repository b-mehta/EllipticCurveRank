/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 228 has rank at least 17

The elliptic curve recorded as
[curve 228](https://elliptic-rank.icarm.cloud/curve/228) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1054784785150680128656`   and
  `a₆ = 13065457517847594395316291335056`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 228 over `ℚ`. -/
@[expose] public def curve228 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -1054784785150680128656, 13065457517847594395316291335056⟩

/-- ICARM leaderboard curve 228 has Mordell-Weil rank at least `17`. -/
public theorem curve228_hasRankGE_17 : HasRankGE curve228 17 := by
  unfold curve228
  certify_curve torsion 29 "data/curve228.txt" "data/curve228-labels.txt"

/-- Curve 228 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve228.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 228. -/
public theorem curve228_j : curve228.j = 126740473530664607703513814623621300307418314495425291967219232836 / 1328511694164589711013308580408399220018420134637453203628825 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
