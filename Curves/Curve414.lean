/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 414 has rank at least 25

The elliptic curve recorded as
[curve 414](https://elliptic-rank.icarm.cloud/curve/414) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -417912674922888853976693575239883106296909250`   and
  `a₆ = 2674272079811740358679570958520093732597884037078754632469690562500`

over `ℚ`. It has Mordell-Weil rank at least `25`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 414 over `ℚ`. -/
@[expose] public def curve414 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -417912674922888853976693575239883106296909250,
    2674272079811740358679570958520093732597884037078754632469690562500⟩

/-- ICARM leaderboard curve 414 has Mordell-Weil rank at least `25`. -/
public theorem curve414_hasRankGE_25 : HasRankGE curve414 25 := by
  unfold curve414
  certify_curve torsion 19 "data/curve414.txt" "data/curve414-labels.txt"

/-- Curve 414 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve414.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 414. -/
public theorem curve414_j : curve414.j = 8071984912151748226445130709682212147192880496269120883693454344965396272976559011876726136366039470197045163491273362864546567398962932001 / 1581739705138847952897657581979669295980470647074499285199050633127943304037864743566952295543770172880782758840137269478960433920000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
