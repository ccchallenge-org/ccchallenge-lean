import CCchallengeLean.Collatz
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Init

/--
Proof of `power_growth` due to Robin Arnez
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Struggling.20with.20simple.20Lemma.3A.203.5Ek.20.20.3E.202.5E.28k.2B1.29.2C.20k.20.3E.3D.202/near/537996466
-/
theorem power_growth
    (k : Nat) (hk : k ≥ 2) :
    (3 : Int)^k > (2 : Int)^(k+1) := by
  norm_cast
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.pow_succ, Nat.mul_assoc, Nat.reduceMul]
  apply Nat.mul_lt_mul_of_le_of_lt
  · apply Nat.pow_le_pow_left
    decide
  · decide
  · apply Nat.pow_pos
    decide


lemma no_small_circuits
  (k: ℕ)
  (l: ℕ)
  (hk: k > 0)
  (hl: l > 0) :
  ((2 : ℤ)^k - 1)*2^l = (3 : ℤ)^k - 1 -> k = 1 ∧ l = 1 := by
  classical
  intro h
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  ------------------------------------------------------------
  -- Step 1: k is odd (reduce mod 3).
  ------------------------------------------------------------
  have hmod3 :
      ((2 : ZMod 3)^k - 1) * (2 : ZMod 3)^l = (3 : ZMod 3)^k - 1 := by
    simpa [map_mul, map_sub, map_pow]
      using congrArg (Int.castRingHom (ZMod 3)) h

  have hkodd : Odd k := by
    -- RHS = -1 in ZMod 3 since k>0 ⇒ 3^k = 0
    have rhs_m1 : (3 : ZMod 3)^k - 1 = (-1 : ZMod 3) := by
      have : (3 : ZMod 3)^k = 0 := by simpa using (zero_pow hk_ne)
      simpa [this]
    have h' : ((2 : ZMod 3)^k - 1) * (2 : ZMod 3)^l = (-1 : ZMod 3) := by
      simpa [rhs_m1] using hmod3
    -- If k even, LHS would be 0 (since (2 = -1), (-1)^even = 1 ⇒ ( … - 1 ) = 0)
    by_contra hnot
    have hkeven : Even k := (Nat.even_or_odd k).resolve_right hnot
    have hLHS0 :
        ((2 : ZMod 3)^k - 1) * (2 : ZMod 3)^l = 0 := by
      have h2 : (2 : ZMod 3) = (-1) := by decide
      have : (2 : ZMod 3)^k = 1 := by
        simpa [h2, Even.neg_one_pow, hkeven]
      simpa [this]
    have : (0 : ZMod 3) = (-1 : ZMod 3) := by simpa [hLHS0] using h'
    cases this

  ------------------------------------------------------------
  -- Step 2: deduce l = 1 (reduce mod 4).
  ------------------------------------------------------------
  have hmod4 :
      ((2 : ZMod 4)^k - 1) * (2 : ZMod 4)^l = (3 : ZMod 4)^k - 1 := by
    simpa [map_mul, map_sub, map_pow]
      using congrArg (Int.castRingHom (ZMod 4)) h

  -- For odd k, (3 : ZMod 4)^k = 3, hence RHS = 2.
  rcases hkodd with ⟨m, hk_eq⟩
  have three_sq4 : (3 : ZMod 4)^2 = 1 := by decide
  have three_pow4 : (3 : ZMod 4)^k = 3 := by
    calc
      (3 : ZMod 4)^k = (3 : ZMod 4)^(2*m + 1) := by simpa [hk_eq]
      _ = (3 : ZMod 4)^(2*m) * 3 := by simp [pow_add]
      _ = ((3 : ZMod 4)^2)^m * 3 := by simpa [pow_mul]
      _ = 1^m * 3 := by simpa [three_sq4]
      _ = 3 := by simp

  have hmod4' :
      ((2 : ZMod 4)^k - 1) * (2 : ZMod 4)^l = (2 : ZMod 4) := by
    simpa [three_pow4] using hmod4

  -- Analyze l: if l≥2 then 2^l = 0 in ZMod 4 → LHS = 0 ≠ 2.
  have hl1 : l = 1 := by
    cases l with
    | zero => cases hl
    | succ l1 =>
      cases l1 with
      | zero => rfl                         -- l = 1
      | succ l2 =>
        -- l = l2 + 2 ≥ 2
        have h2sq : (2 : ZMod 4)^2 = 0 := by decide
        have : (2 : ZMod 4) ^ (l2 + 1 + 1) = 0 := by
          -- first rewrite l2+1+1 = l2+2
          have : (2 : ZMod 4) ^ (l2 + 2) = 0 := by
            calc
              (2 : ZMod 4) ^ (l2 + 2)
                  = (2 : ZMod 4) ^ l2 * (2 : ZMod 4) ^ 2 := by
                      simpa [pow_add]
              _   = (2 : ZMod 4) ^ l2 * 0 := by simpa [h2sq]
              _   = 0 := by simp
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using this
        have : (2 : ZMod 4)^(Nat.succ (Nat.succ l2)) = 0 := by
          -- (2^(l2+2)) = (2^2)*(2^l2) = 0
          simpa [Nat.succ_eq_add_one, pow_add, h2sq]
        have : (0 : ZMod 4) = (2 : ZMod 4) := by
          simpa [this] using hmod4'
        cases this

  have hkodd : Odd k := ⟨m, hk_eq⟩

  simp [hl1] at h

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

  have lgrowth : k ≥ 3 -> (3 : ℤ)^k > (2 : ℤ)^(k+1) := by
    intro hkgeq3
    have hkgeq2 : k ≥ 2 := Nat.le_trans (by decide : 3 ≥ 2) hkgeq3

    apply power_growth
    assumption

  have h'' : ¬ 3 ≤ k := by
    intro hk3
    have hgt : (2 : ℤ) ^ (k + 1) < (3 : ℤ) ^ k := by
      simpa [gt_iff_lt] using lgrowth hk3
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

  exact ⟨hkone, hl1⟩
