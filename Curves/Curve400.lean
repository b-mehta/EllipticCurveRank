/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 400 has rank at least 28

The elliptic curve recorded as
[curve 400](https://elliptic-rank.icarm.cloud/curve/400) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2847874483810983397135985687546115504035875512904930`   and
  `a₆ = 5863572094560733325227696745989482992866153015698157430026855716216140568890`
  `     0`

over `ℚ`. It has Mordell-Weil rank at least `28`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve400.txt`; descent labels are in
`data/curve400-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 400 over `ℚ`. -/
@[expose] public def curve400 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2847874483810983397135985687546115504035875512904930,
    58635720945607333252276967459894829928661530156981574300268557162161405688900⟩

/-- ICARM leaderboard curve 400 has Mordell-Weil rank at least `28`. -/
public theorem curve400_hasRankGE_28 : HasRankGE curve400 28 := by
  unfold curve400
  certify_curve torsion 59 "data/curve400.txt" "data/curve400-labels.txt"

/-- Curve 400 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve400.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 400. -/
public theorem curve400_j : curve400.j = -19600711737340767304288459746432757739234884166585359113045472471831472218851230852454819678973320927957846652371235395016530064436511753445538311041584401 / 54082998607154326540304542174041830004035093037632269656999561270139165468667949739950022203221233657912677019623272103774809531076287997909504000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
