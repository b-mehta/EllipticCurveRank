/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Raw kernel primitives as notation
-/

@[simp, grind =] theorem Nat.mod_eq_mod : Nat.mod a b = a % b := rfl

@[simp, grind =] theorem Int.sub_eq : Int.sub a b = a - b := rfl

@[simp, grind =] theorem Int.neg_eq : Int.neg a = -a := rfl

@[simp, grind =] theorem Int.emod_eq : Int.emod a b = a % b := rfl

attribute [grind =] Nat.add_eq Nat.mul_eq
