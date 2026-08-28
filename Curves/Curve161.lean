/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 161 has rank at least 18

The elliptic curve recorded as
[curve 161](https://elliptic-rank.icarm.cloud/curve/161) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -186119222080171360016717948`   and
  `a₆ = 966784961134576267766275148260409718847`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve161.txt`; descent labels are in
`data/curve161-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 161 over `ℚ`. -/
@[expose] public def curve161 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -186119222080171360016717948, 966784961134576267766275148260409718847⟩

/-- ICARM leaderboard curve 161 has Mordell-Weil rank at least `18`. -/
public theorem curve161_hasRankGE_18 : HasRankGE curve161 18 := by
  unfold curve161
  certify_curve torsion 29 "data/curve161.txt" "data/curve161-labels.txt"

/-- Curve 161 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve161.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 161. -/
public theorem curve161_j : curve161.j = 978069845987190219492765352210406447073078833062050197757170032769826714119690361 / 12132250605020013493243096665689064764549047379624266082874463921324362956800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
