import UniformProductChernoff
import Mathlib.Tactic

/-!
# Coupon estimates for the fixed-quota lower bound

These are unconditional finite probability statements for independent uniform
labels. They do not yet identify the raw-label process with `ReplicaPS`.
In particular this module alone does not prove a lower bound for PS rank.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.CouponLowerBound
open UniformProduct

def labelSample (m k : ℕ) : Finset (Fin k → Fin m) :=
  productSample Finset.univ k

def avoids {m : ℕ} (g x : Fin m) : ℝ := if x = g then 0 else 1

def unseenIndicator {m k : ℕ} (g : Fin m) (w : Fin k → Fin m) : ℝ :=
  ∏ i, avoids g (w i)

def unseenCount {m k : ℕ} (w : Fin k → Fin m) : ℝ :=
  ∑ g, unseenIndicator g w

def meanUnseen (m k : ℕ) : ℝ := (m : ℝ) * (1 - 1 / (m : ℝ)) ^ k

lemma avoids_nonneg {m : ℕ} (g x : Fin m) : 0 ≤ avoids g x := by
  unfold avoids
  split_ifs <;> norm_num

lemma unseenIndicator_nonneg {m k : ℕ} (g : Fin m) (w : Fin k → Fin m) :
    0 ≤ unseenIndicator g w :=
  Finset.prod_nonneg (fun i _ => avoids_nonneg g (w i))

lemma unseenCount_nonneg {m k : ℕ} (w : Fin k → Fin m) : 0 ≤ unseenCount w :=
  Finset.sum_nonneg (fun g _ => unseenIndicator_nonneg g w)

lemma unseenIndicator_mul_self {m k : ℕ} (g : Fin m) (w : Fin k → Fin m) :
    unseenIndicator g w * unseenIndicator g w = unseenIndicator g w := by
  unfold unseenIndicator
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : w i = g <;> simp [avoids, h]

lemma expect_avoids {m : ℕ} (hm : 0 < m) (g : Fin m) :
    (𝔼 x : Fin m, avoids g x) = 1 - 1 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hx (x : Fin m) : avoids g x = 1 - (if x = g then (1 : ℝ) else 0) := by
    by_cases h : x = g <;> simp [avoids, h]
  simp_rw [hx]
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

theorem expected_unseenIndicator {m : ℕ} (hm : 0 < m) (k : ℕ) (g : Fin m) :
    (𝔼 w ∈ labelSample m k, unseenIndicator g w) = (1 - 1 / (m : ℝ)) ^ k := by
  change (𝔼 w ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin m))),
    ∏ i, avoids g (w i)) = _
  rw [← Finset.expect_pow, expect_avoids hm]

theorem expected_unseenCount {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (𝔼 w ∈ labelSample m k, unseenCount w) = meanUnseen m k := by
  unfold unseenCount
  rw [Finset.expect_sum_comm]
  simp_rw [expected_unseenIndicator hm k]
  simp [meanUnseen]

lemma expect_avoids_pair {m : ℕ} (hm : 0 < m) (g h : Fin m) (hne : g ≠ h) :
    (𝔼 x : Fin m, avoids g x * avoids h x) = 1 - 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hx (x : Fin m) : avoids g x * avoids h x =
      1 - (if x = g then (1 : ℝ) else 0) - (if x = h then (1 : ℝ) else 0) := by
    by_cases hg : x = g
    · subst x
      simp [avoids, hne]
    · by_cases hh : x = h <;> simp [avoids, hg, hh, Ne.symm hne]
  simp_rw [hx]
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  <;> ring

theorem expected_unseen_pair {m : ℕ} (hm : 0 < m) (k : ℕ)
    (g h : Fin m) (hne : g ≠ h) :
    (𝔼 w ∈ labelSample m k, unseenIndicator g w * unseenIndicator h w) =
      (1 - 2 / (m : ℝ)) ^ k := by
  simp only [unseenIndicator, ← Finset.prod_mul_distrib]
  change (𝔼 w ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin m))),
    ∏ i, (avoids g (w i) * avoids h (w i))) = _
  rw [← Finset.expect_pow Finset.univ (fun x : Fin m => avoids g x * avoids h x) k,
    expect_avoids_pair hm g h hne]

theorem unseen_pair_nonpositive_covariance {m : ℕ} (hm : 2 ≤ m) (k : ℕ)
    (g h : Fin m) (hne : g ≠ h) :
    (𝔼 w ∈ labelSample m k, unseenIndicator g w * unseenIndicator h w) ≤
      (𝔼 w ∈ labelSample m k, unseenIndicator g w) *
        (𝔼 w ∈ labelSample m k, unseenIndicator h w) := by
  have hmpos : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  rw [expected_unseen_pair hmpos k g h hne,
    expected_unseenIndicator hmpos k, expected_unseenIndicator hmpos k]
  have hbase0 : 0 ≤ 1 - 2 / (m : ℝ) := by
    have := (div_le_one hm0).2 hmR
    linarith
  have hbase : 1 - 2 / (m : ℝ) ≤ (1 - 1 / (m : ℝ)) ^ 2 := by
    simp only [div_eq_mul_inv, one_mul]
    nlinarith [sq_nonneg ((m : ℝ)⁻¹)]
  have hp := pow_le_pow_left₀ hbase0 hbase k
  simpa only [pow_two, mul_pow] using hp

theorem unseen_second_moment_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    (𝔼 w ∈ labelSample m k, (unseenCount w) ^ 2) ≤
      (meanUnseen m k) ^ 2 + meanUnseen m k := by
  have hmpos : 0 < m := by omega
  let p : ℝ := (1 - 1 / (m : ℝ)) ^ k
  have hp : 0 ≤ p := by
    apply pow_nonneg
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
    linarith [(div_le_one hm0).2 hmR]
  have hpair (g h : Fin m) :
      (𝔼 w ∈ labelSample m k, unseenIndicator g w * unseenIndicator h w) ≤
        p * p + if g = h then p else 0 := by
    by_cases hgh : g = h
    · subst h
      simp only [unseenIndicator_mul_self, expected_unseenIndicator hmpos k, if_true]
      dsimp [p]
      nlinarith [sq_nonneg p]
    · have hc := unseen_pair_nonpositive_covariance hm k g h hgh
      simpa only [expected_unseenIndicator hmpos k, if_neg hgh, add_zero] using hc
  calc
    (𝔼 w ∈ labelSample m k, (unseenCount w) ^ 2) =
        ∑ g : Fin m, ∑ h : Fin m,
          𝔼 w ∈ labelSample m k, unseenIndicator g w * unseenIndicator h w := by
      simp only [unseenCount, pow_two, Finset.sum_mul_sum]
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ g : Fin m, ∑ h : Fin m, (p * p + if g = h then p else 0) := by
      apply Finset.sum_le_sum
      intro g hg
      exact Finset.sum_le_sum (fun h _ => hpair g h)
    _ = (meanUnseen m k) ^ 2 + meanUnseen m k := by
      simp [Finset.sum_add_distrib, meanUnseen, p]
      <;> ring

theorem unseen_variance_le_mean {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    (𝔼 w ∈ labelSample m k, (unseenCount w - meanUnseen m k) ^ 2) ≤
      meanUnseen m k := by
  have hmpos : 0 < m := by omega
  have hs : (labelSample m k).Nonempty :=
    productSample_nonempty ⟨⟨0, hmpos⟩, Finset.mem_univ _⟩ k
  have hexpand (w : Fin k → Fin m) :
      (unseenCount w - meanUnseen m k) ^ 2 =
        (unseenCount w) ^ 2 - (2 * meanUnseen m k) * unseenCount w +
          (meanUnseen m k) ^ 2 := by ring
  simp_rw [hexpand]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, expected_unseenCount hmpos k, Finset.expect_const hs]
  nlinarith [unseen_second_moment_le hm k]

theorem meanUnseen_pos {m : ℕ} (hm : 2 ≤ m) (k : ℕ) : 0 < meanUnseen m k := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hm0 : (0 : ℝ) < m := by linarith
  apply mul_pos hm0
  apply pow_pos
  have := (div_lt_one hm0).2 hmR
  linarith

theorem unseen_lower_tail {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    probability (labelSample m k)
      (fun w => unseenCount w < meanUnseen m k / 2) ≤ 4 / meanUnseen m k := by
  let μ := meanUnseen m k
  have hμ : 0 < μ := meanUnseen_pos hm k
  have hmarkov := UniformProduct.markov (labelSample m k)
    (fun w => unseenCount w < μ / 2)
    (fun w => (unseenCount w - μ) ^ 2)
    (a := μ ^ 2 / 4) (by positivity)
    (fun _ _ => sq_nonneg _)
    (by
      intro w hw hlow
      have hs := sq_nonneg (unseenCount w - μ / 2)
      nlinarith)
  have hv := unseen_variance_le_mean hm k
  change _ ≤ μ at hv
  have h := hmarkov.trans hv
  apply (le_div_iff₀ hμ).2
  nlinarith [sq_pos_of_pos hμ]

end ProbabilisticSerial.CouponLowerBound
