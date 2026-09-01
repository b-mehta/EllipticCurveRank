/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 442 has rank at least 19

The elliptic curve recorded as
[curve 442](https://elliptic-rank.icarm.cloud/curve/442) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -13726712801000904290088341272158565293041168623859938751245316012367`   and
  `a₆ = 1955875560529943535626645088989724445237788586648372210387930316688496162406`
  `     7395928673936320669626391`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by Nikita-Shulga.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 442 over `ℚ`. -/
@[expose] public def curve442 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -13726712801000904290088341272158565293041168623859938751245316012367,
    19558755605299435356266450889897244452377885866483722103879303166884961624067395928673936320669626391⟩

/-- ICARM leaderboard curve 442 has Mordell-Weil rank at least `19`. -/
public theorem curve442_hasRankGE_19 : HasRankGE curve442 19 := by
  unfold curve442
  certify_curve torsion 17 "data/curve442.txt" "data/curve442-labels.txt"

/-- Curve 442 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve442.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 442. -/
public theorem curve442_j : curve442.j = 286037750344281590453843275485271804393140348410973813976206475615081128967967788408213684830902802698369091662283756233791838549125573363988873993730018800004605585640863900864693943116588610376037244660801 / 271699725687646192733286577518625031822437545106002056586462275802181671252630486164380611220824656488577659302044450835197610654138474077293389412541369981252145070435260693284903863672927060480000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
