/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 316 has rank at least 17

The elliptic curve recorded as
[curve 316](https://elliptic-rank.icarm.cloud/curve/316) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1185784901231914789559558181`   and
  `a₆ = 15709973088316374222740088167179617119361`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Jack Cheng.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 316 over `ℚ`. -/
@[expose] public def curve316 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1185784901231914789559558181, 15709973088316374222740088167179617119361⟩

/-- ICARM leaderboard curve 316 has Mordell-Weil rank at least `17`. -/
public theorem curve316_hasRankGE_17 : HasRankGE curve316 17 := by
  unfold curve316
  certify_curve torsion 29 "data/curve316.txt" "data/curve316-labels.txt"

/-- Curve 316 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve316.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 316. -/
public theorem curve316_j : curve316.j = 184391739121880065105208192710402274808760053284557828001218670228487988047900806178769 / 89176446007892832942170673747379791745757428321235958497602360325335450136985600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
