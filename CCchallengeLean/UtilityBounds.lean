import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

open Nat

/-!
# Utility bounds

Collection of utility bounds.
-/

/--
If `n ≠ 0`, then `2^n < 3^n`.
-/
lemma pow_two_lt_pow_three (n : ℕ) (h : n ≠ 0) : 2^n < 3^n :=
  Nat.pow_lt_pow_left (by decide) (h)

/--
If `a ≥ 2` and `c ≥ 1`, then `a^(b + c) > a^b`.
-/
lemma pow_strict_mono_of_base_ge_two {a : ℕ} {b c : ℕ} (h_base : a ≥ 2) (h_c : c ≥ 1) :
    a ^ (b + c) > a ^ b := by
  -- We can use the identity: a^(b + c) = a^b * a^c
  rw [Nat.pow_add]
  -- Show that a^c > 1
  have a_pow_c_gt_one : a ^ c > 1 := by
    have h_a_pos : a > 0 := by linarith [h_base]
    have : a ^ c ≥ a ^ 1 := Nat.pow_le_pow_right h_a_pos h_c
    have : a ^ 1 = a := Nat.pow_one a
    have : a ≥ 2 := h_base
    linarith
  -- Now a^b * a^c > a^b * 1 = a^b
  have a_pow_b_pos : a ^ b > 0 := Nat.pow_pos (by linarith [h_base])
  have : a ^ b * a ^ c > a ^ b * 1 :=
    (Nat.mul_lt_mul_left a_pow_b_pos).mpr a_pow_c_gt_one
  rw [Nat.mul_one] at this
  exact this
