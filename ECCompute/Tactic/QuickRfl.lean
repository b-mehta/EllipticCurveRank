/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Lean

/-!
# The `quickRfl` tactic

`quickRfl` closes a goal of the form `b = true` for a `Bool` expression `b` by assigning
`Lean.reflBoolTrue`, so the kernel reduces `b` to `true` directly. The project discharges its
kernel-reducible `Bool` certificate obligations with it: the `checkLabel`, `checkInv`,
`hasRootMod`, and j-invariant checks.
-/

/-- Close a goal `b = true` (`b : Bool`) by kernel reduction, via `Lean.reflBoolTrue`. -/
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue
