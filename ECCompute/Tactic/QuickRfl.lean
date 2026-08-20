/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Lean

/-!
# The `quickRfl` tactic

`quickRfl` closes a goal of the form `b = true` for a `Bool` expression `b` by assigning
`Lean.reflBoolTrue`, so the kernel reduces `b` to `true` directly. The project uses it for the
discriminant check behind `IsElliptic` and for the `j`-invariant checks in `Check.JInvariant`.
-/

/-- Close a goal `b = true` (`b : Bool`) by kernel reduction, via `Lean.reflBoolTrue`. -/
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue
