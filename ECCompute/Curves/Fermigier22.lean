/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# Fermigier's curve has rank at least 22

Fermigier's elliptic curve

  `E : y² + xy + y = x³ - 940299517776391362903023121165864 x`
  `                  + 10707363070719743033425295515449274534651125011362`

over `ℚ` has Mordell-Weil rank at least `22`, the 1997 rank record of S. Fermigier. Points in
`data/fermigier22.txt`, descent labels in `data/fermigier22-labels.txt`; `certify_curve` does the
rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- Fermigier's rank-22 elliptic curve over `ℚ`. Certified rank ≥ 22 in
`curveFermigier22_hasRankGE_22`. -/
def curveFermigier22 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -940299517776391362903023121165864,
    10707363070719743033425295515449274534651125011362⟩

/-- Fermigier's curve has Mordell-Weil rank at least `22`. -/
theorem curveFermigier22_hasRankGE_22 : HasRankGE curveFermigier22 22 := by
  unfold curveFermigier22
  certify_curve torsion 31 points "data/fermigier22.txt" labels "data/fermigier22-labels.txt"

end ECCompute
