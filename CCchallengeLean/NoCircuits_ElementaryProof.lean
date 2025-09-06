import CCchallengeLean.Collatz
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

lemma power_growth
  (k: ℕ)
  (hk: Odd k ∧ k ≥ 3) : 3^k > 2^(k+1) := by sorry

lemma yes : (-1 : ℤ) + 2 = 1 := by
  have h : (-1 : ℤ) + 1 = 0 := by simp
  simpa using add_right_cancel (by
    -- add 1 to both sides of h
    simpa [add_assoc] using congrArg (fun t => t + 1) h : (-1 : ℤ) + 2 = 1 + 0)


example (k : ℕ) (hk : k < 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  interval_cases k
  all_goals simp


lemma no_small_circuits
  (k: ℕ)
  (l: ℕ)
  (hk: k > 0)
  (hl: l > 0) :
  ((2 : ℤ)^k - 1)*2^l = (3 : ℤ)^k - 1 -> k = 1 ∧ l = 1 := by
  intro h
  have hodd : Odd k := by sorry
  have hlone : l = 1 := by sorry
  simp [hlone] at h
  have lgrowth : Odd k ∧ k ≥ 3 -> (3 : ℤ)^k > (2 : ℤ)^(k+1) := by sorry
  rw [sub_mul] at h
  simp at h
  replace h := congrArg (fun t : ℤ => t + 2) h
  ring_nf at h
  rw [<- pow_succ] at h
  have h' : (3 : ℤ)^k < 2^(k+1) := by
    have : (3 : ℤ) ^ k < (3 : ℤ) ^ k + 1 := by
      have : (0 : ℤ) < 1 := by decide
      simpa using lt_add_of_pos_right ((3 : ℤ) ^ k) this
    simpa [h, add_comm] using this

  have h'' : ¬ 3 ≤ k := by
    intro hk3
    have hgt : (2 : ℤ) ^ (k + 1) < (3 : ℤ) ^ k := by
      simpa [gt_iff_lt] using lgrowth ⟨hodd, hk3⟩
    exact lt_asymm h' hgt

  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by
    interval_cases k
    all_goals simp

  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk

  have hkone : k = 1 := by
    rcases hk_cases with rfl | rfl | rfl
    · -- case k = 0: contradicts hk
      exact (hk_ne rfl).elim
    · -- case k = 1: done
      rfl
    · -- case k = 2: compute the equation → 8 = 10 (absurd)
      -- turn the goal into False and discharge by computation
      exfalso
      have h' : (2 : ℕ) ^ (2 + 1) = 1 + 3 ^ 2 := by simpa using h
      exact (by decide : (2 : ℕ) ^ (2 + 1) ≠ 1 + 3 ^ 2) h'

  exact ⟨hkone, hlone⟩



















  -- intermediate result established; remaining steps omitted for now
  sorry
