import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

open Nat

lemma pow_two_lt_pow_three (n : ℕ) (h : n ≠ 0) : 2^n < 3^n :=
  Nat.pow_lt_pow_left (by decide) (h)

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

lemma magic_factorization_positive
    (k n : ℕ)
    (hk : k > 0) -- This is for 2^0 + 6*9^0 > 7*6^0
    (hn : n > 0)
    (h : 2^n > 3^k) :
    (3^(k+1) - 2^(k+1)) * (2^n - 3^k) * (2^(k+n) + 2 * 3^(2*k+1) - 7 * 6^k) > 0 := by
  -- Use your lemma
  have h1 : 2^(k+1) < 3^(k+1) := pow_two_lt_pow_three (k+1) (Nat.succ_ne_zero k)
  have pos1 : 3^(k+1) - 2^(k+1) > 0 := Nat.sub_pos_of_lt h1
  have pos2 : 2^n - 3^k > 0 := Nat.sub_pos_of_lt h
  suffices h2 : 2^(k+n) + 2 * 3^(2*k+1) - 7 * 6^k > 0 by
    exact Nat.mul_pos (Nat.mul_pos pos1 pos2) h2
  suffices h3 : 2^k + 2 * 3^(2*k+1) - 7 * 6^k > 0 by
    -- Use pow_strict_mono_of_base_ge_two to show 2^(k+n) > 2^k
    have h_mono : 2^(k+n) > 2^k :=
      pow_strict_mono_of_base_ge_two (le_refl 2) hn
    -- Since 2^(k+n) > 2^k and everything else is the same, the inequality holds
    have h_pos : 2^k > 0 := Nat.pow_pos (by norm_num)
    omega  -- omega should handle this arithmetic
  -- Case analysis on k
  cases Nat.eq_zero_or_pos k with
  | inl hk_zero =>
    -- Case k = 0: This contradicts our hypothesis hk : k > 0
    exfalso
    rw [hk_zero] at hk
    exact Nat.lt_irrefl 0 hk
  | inr hk_pos =>
    -- Case k > 0: This is consistent with our hypothesis hk : k > 0
    -- First, let's rewrite 2 * 3^(2*k+1) as 6 * 9^k
    have h_rewrite : 2 * 3^(2*k+1) = 6 * 9^k := by
      -- Prove: 2*3^(2*k+1) = 2*((3^2)^k)*3 = 6*9^k
      calc 2 * 3^(2*k+1)
        = 2 * (3^(2*k) * 3) := by rw [Nat.pow_succ]
        _ = 2 * 3^(2*k) * 3 := by rw [Nat.mul_assoc]
        _ = 2 * (3^2)^k * 3 := by rw [Nat.pow_mul]
        _ = 2 * 9^k * 3 := by norm_num
        _ = 6 * 9^k := by ring
    -- Now we need to show: 2^k + 6 * 9^k - 7 * 6^k > 0
    rw [h_rewrite]
    -- Since 6 * 9 = 54 > 42 = 7 * 6, we have 6 * 9^k > 7 * 6^k for k > 0
    -- Therefore 2^k + 6 * 9^k > 2^k + 7 * 6^k ≥ 7 * 6^k
    -- So 2^k + 6 * 9^k - 7 * 6^k > 0
    have key_ineq : 6 * 9^k > 7 * 6^k := by
      -- Rewrite as: 54 * 9^(k-1) > 42 * 6^(k-1)
      -- Since k > 0, we have k.pred + 1 = k
      have hk_eq : k.pred.succ = k := Nat.succ_pred_eq_of_pos hk_pos
      -- Rewrite 6 * 9^k = 6 * 9 * 9^(k-1) = 54 * 9^(k-1)
      have h_left : 6 * 9^k = 54 * 9^k.pred := by
        rw [← hk_eq, Nat.pow_succ]
        simp only [Nat.succ_pred_eq_of_pos hk_pos]
        ring
      -- Rewrite 7 * 6^k = 7 * 6 * 6^(k-1) = 42 * 6^(k-1)
      have h_right : 7 * 6^k = 42 * 6^k.pred := by
        rw [← hk_eq, Nat.pow_succ]
        simp only [Nat.succ_pred_eq_of_pos hk_pos]
        ring
      -- We need to show 6 * 9^k > 7 * 6^k, which we've rewritten as 54 * 9^(k-1) > 42 * 6^(k-1)
      rw [h_left, h_right]
      -- Since 54 > 42 and 9^(k-1) ≥ 6^(k-1), the result follows
      have h_54_gt_42 : (54 : ℕ) > 42 := by norm_num
      have h_pos_9 : 9^k.pred > 0 := Nat.pow_pos (by norm_num)
      -- We use: 54 * 9^(k-1) > 42 * 9^(k-1) ≥ 42 * 6^(k-1)
      -- The first inequality uses 54 > 42
      have h_step1 : 42 * 9^k.pred < 54 * 9^k.pred := by
        exact Nat.mul_lt_mul_of_pos_right h_54_gt_42 h_pos_9
      -- The second inequality uses 6^(k-1) ≤ 9^(k-1) (since 6 ≤ 9)
      have h_6_le_9 : (6 : ℕ) ≤ 9 := by norm_num
      have h_step2 : 42 * 6^k.pred ≤ 42 * 9^k.pred := by
        apply Nat.mul_le_mul_left
        -- Show 6^k.pred ≤ 9^k.pred by induction
        induction k.pred with
        | zero => simp
        | succ m ih =>
          simp only [Nat.pow_succ]
          exact Nat.mul_le_mul ih (by norm_num : 6 ≤ 9)
      -- Combine them
      exact lt_of_le_of_lt h_step2 h_step1

    have h_pos : 2^k > 0 := Nat.pow_pos (by norm_num)
    -- Since 6 * 9^k > 7 * 6^k and 2^k > 0, we have 2^k + 6 * 9^k > 7 * 6^k
    have : 2^k + 6 * 9^k > 7 * 6^k := by linarith [key_ineq, h_pos]
    -- Therefore 2^k + 6 * 9^k - 7 * 6^k > 0
    exact Nat.sub_pos_of_lt this

def max_circuit_element (n k : ℤ) : ℚ :=
  2^(n-k)*(3^k-2^k)/(2^n - 3^k)

def max_circuit_element_ratio_k (n k : ℤ) : ℚ :=
  (max_circuit_element n (k) : ℚ) / (max_circuit_element n (k+1) : ℚ)

def max_circuit_element_ratio_k_rewritten (n k : ℤ) : ℚ :=
  2*(3^k - 2^k)*(2^n - 3^(k+1)) /
  ((2^n - 3^k)*(3^(k+1) - 2^(k+1)))

lemma pow_two_diff (n k : ℤ) : (2 : ℚ) ^ (n - k) / 2 ^ (n - k - 1) = 2 := by
  rw [← zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring
  ring

lemma isolate_power_factor (n k : ℤ) (A B C D: ℚ) :
  (2 ^ (n - k) * A * B) / (C *(2 ^ (n - k - 1) * D)) =
  (2 ^ (n - k) / 2 ^ (n - k - 1)) * (A * B / (C * D)) := by
  field_simp
  ring

-- Statement of the ratio result
lemma max_circuit_element_ratio (n k : ℤ) :
    max_circuit_element_ratio_k n k = max_circuit_element_ratio_k_rewritten n k := by
  -- This is standard algebra - the proof involves:
  unfold max_circuit_element_ratio_k max_circuit_element_ratio_k_rewritten max_circuit_element

  -- Step 1: Apply the division rule using div_div_div_eq
  -- We have: (a / b) / (c / d) = (a * d) / (b * c)
  rw [div_div_div_eq]

  -- Step 2: Simplify n - (k+1) = n - k - 1
  -- Use explicit rewrite with the subtraction identity
  rw [show ∀ n k : ℤ, n - (k + 1) = n - k - 1 by intros; omega]

  rw [isolate_power_factor]
  rw [pow_two_diff]
  ring
