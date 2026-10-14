import CouponLowerBound
import ReplicaUntouched

/-! Coupon counts are the cardinalities of actual untouched-type sets. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.CouponLowerBound

def untouchedTypes {m k : ℕ} (w : Fin k → Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun g => ∀ i, w i ≠ g)

@[simp] lemma mem_untouchedTypes {m k : ℕ} (w : Fin k → Fin m) (g : Fin m) :
    g ∈ untouchedTypes w ↔ ∀ i, w i ≠ g := by simp [untouchedTypes]

lemma unseenIndicator_eq_untouched {m k : ℕ} (g : Fin m) (w : Fin k → Fin m) :
    unseenIndicator g w = if g ∈ untouchedTypes w then 1 else 0 := by
  by_cases hg : g ∈ untouchedTypes w
  · have havoid := (mem_untouchedTypes w g).1 hg
    simp [unseenIndicator, avoids, havoid, hg]
  · have hex : ∃ i, w i = g := by simpa using hg
    obtain ⟨i, hi⟩ := hex
    rw [if_neg hg]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [avoids, hi]

theorem unseenCount_eq_card {m k : ℕ} (w : Fin k → Fin m) :
    unseenCount w = (untouchedTypes w).card := by
  unfold unseenCount
  simp_rw [unseenIndicator_eq_untouched]
  simp [untouchedTypes]

theorem untouched_card_lower_tail {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    UniformProduct.probability (labelSample m k)
      (fun w => ((untouchedTypes w).card : ℝ) < meanUnseen m k / 2) ≤
      4 / meanUnseen m k := by
  simpa only [unseenCount_eq_card] using unseen_lower_tail hm k

theorem untouched_full_quota {m q : ℕ} [Nonempty (Fin (m * q))]
    (reference : ReplicaPS.Profile m q) (k : ℕ) (w : Fin k → Fin m) :
    (∑ g ∈ untouchedTypes w,
      ReplicaChoiceMachine.residual
        ((ReplicaRawProcess.initialState reference).evolve k w).reference
        ((ReplicaRawProcess.initialState reference).evolve k w).clock g) =
      q * ((untouchedTypes w).card : ℝ) := by
  calc
    _ = ∑ _g ∈ untouchedTypes w, (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact ReplicaUntouched.untouched_residual_eq_quota reference k w g
        ((mem_untouchedTypes w g).1 hg)
    _ = _ := by simp [mul_comm]

theorem meanUnseen_ge_exponential {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    (m : ℝ) * Real.exp (-(2 * k / (m : ℝ))) ≤ meanUnseen m k := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hu : 0 ≤ 1 / (m : ℝ) := by positivity
  have hu2 : 1 / (m : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hmR
  have hx : 0 < 1 - 1 / (m : ℝ) := by linarith
  have hinv : (1 - 1 / (m : ℝ))⁻¹ ≤ 1 + 2 / m := by
    rw [← one_div]
    apply (div_le_iff₀ hx).2
    have heq : (1 + 2 / (m : ℝ)) * (1 - 1 / (m : ℝ)) =
        1 + (1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) := by ring
    rw [heq]
    have hz : 0 ≤ 1 - 2 / (m : ℝ) := by
      have h := (div_le_one hmpos).2 hmR
      linarith
    nlinarith [mul_nonneg hu hz]
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hloglower : -(2 / (m : ℝ)) ≤ Real.log (1 - 1 / (m : ℝ)) := by linarith
  unfold meanUnseen
  apply mul_le_mul_of_nonneg_left _ hmpos.le
  rw [← Real.exp_log hx, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hloglower (Nat.cast_nonneg k)
  convert h using 1 <;> ring

end ProbabilisticSerial.CouponLowerBound
