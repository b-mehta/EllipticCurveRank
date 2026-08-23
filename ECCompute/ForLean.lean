/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Raw kernel primitives as notation
-/

public section

@[simp, grind =] theorem Nat.mod_eq_mod : Nat.mod a b = a % b := rfl

@[simp, grind =] theorem Int.sub_eq : Int.sub a b = a - b := rfl

@[simp, grind =] theorem Int.neg_eq : Int.neg a = -a := rfl

@[simp, grind =] theorem Int.emod_eq : Int.emod a b = a % b := rfl

@[simp, grind =]
theorem Nat.beq_eq_beq : Nat.beq a b = (a == b) := by rw [Bool.eq_iff_iff]; simp

attribute [grind =] Nat.add_eq Nat.mul_eq Nat.ble_eq
attribute [grind =] Int.add_def Int.mul_def
attribute [grind =] Bool.and'_eq_and Bool.not'_eq_not Bool.or'_eq_or
