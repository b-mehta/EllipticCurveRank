/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.MainTheorem

/-!
# Comparator challenge: curve 302 has rank at least 31

Trusted, independent statement of `ECCompute.curve302_hasRankGE_31` for the
[`leanprover/comparator`](https://github.com/leanprover/comparator) adversarial check.

This module restates the theorem from its own copy of the curve-302 a-invariants together with the
`HasRankGE` predicate imported from `ECCompute.MainTheorem`, leaving the proof as `sorry`. It does
*not* import `ECCompute.Curves.Curve302`, so the statement here is fixed independently of the real
proof. The comparator then verifies that the solution module `ECCompute.Curves.Curve302` proves
exactly this statement, using no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

The a-invariants and target rank must be kept identical to `ECCompute/Curves/Curve302.lean`.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 302 over `ℚ` (independent copy for the comparator challenge). -/
def curve302 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1284727764113567728281797636015784768866707681415849262157224232063,
    560368321454261339256859338901915312332769858684945406858043869199456710681989058863306170127006181⟩

/-- ICARM leaderboard curve 302 has Mordell-Weil rank at least `31`. -/
theorem curve302_hasRankGE_31 : HasRankGE curve302 31 := sorry

end ECCompute
