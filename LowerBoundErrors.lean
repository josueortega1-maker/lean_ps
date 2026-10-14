import FiniteLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Elementary rates and vanishing finite-market error terms. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundErrors
open ReplicaRawCostRank ReplicaLowerRank LowerBoundEntropy FiniteLowerBound

theorem count_rate_pos {α : ℝ} (hα : 1 < α) : 0 < α - 1 - Real.log α := by
  have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < α) (by linarith : α ≠ 1)
  linarith

theorem coarse_rate_pos : 0 < 3 - Real.log 4 - Real.log 2 := by
  have hlog : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  rw [h4]
  linarith

theorem smallSets_card_bound (m hi : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hhi : (hi : ℝ) ≤ m * Real.exp (-B)) :
    ((smallSets m hi).card : ℝ) ≤ Real.exp (((B + 1) * Real.exp (-B)) * m) := by
  apply small_family_card_le_rate m hi (smallSets m hi) hB _ hhi
  intro S hS
  exact (Finset.mem_filter.mp hS).2

theorem activeSizeBand_card_bound (m lo hi : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hhi : (hi : ℝ) ≤ m * Real.exp (-B)) :
    ((activeSizeBand m lo hi).card : ℝ) ≤ Real.exp (((B + 1) * Real.exp (-B)) * m) := by
  apply small_family_card_le_rate m hi (activeSizeBand m lo hi) hB _ hhi
  intro S hS
  exact ((mem_activeSizeBand S).1 hS).2.2

lemma exponential_family_error {m q : ℕ} (hq : 0 < q)
    {size rate ρ c : ℝ} (hsize : 0 ≤ size)
    (hcard : size ≤ Real.exp (ρ * m)) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hrate : c + ρ ≤ rate) :
    size * Real.exp (-rate * (m * q : ℕ)) ≤ Real.exp (-c * m) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hrate0 : 0 ≤ rate := by linarith
  calc
    _ ≤ Real.exp (ρ * m) * Real.exp (-rate * (m * q : ℕ)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (ρ * m - rate * (m * q : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-c * m) := by
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_mul]
      have h1 := mul_le_mul_of_nonneg_left hqR (mul_nonneg hrate0 hmR)
      have h2 := mul_le_mul_of_nonneg_right hrate hmR
      nlinarith

theorem exceptionalBound_le {m q N lo hi : ℕ} (hq : 0 < q)
    {α θ a K B c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hhi : (hi : ℝ) ≤ m * Real.exp (-B))
    (hcoarse : c + Real.log 2 ≤ 3 - Real.log 4)
    (hfine : c + (B + 1) * Real.exp (-B) ≤ α - 1 - Real.log α)
    (hrank : c + (B + 1) * Real.exp (-B) ≤
      θ * (a - K) - θ ^ 2 * (16 * (1 + Real.exp 1))) :
    exceptionalBound m q N lo hi α θ a K ≤
      ((2 : ℝ) * (N + 1 : ℕ) + 1) * Real.exp (-c * m) := by
  have hρ : 0 ≤ (B + 1) * Real.exp (-B) := by positivity
  have hcard : (2 : ℝ) ^ m ≤ Real.exp (Real.log 2 * m) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h1 := exponential_family_error hq (by positivity : 0 ≤ (2 : ℝ) ^ m) hcard hc
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hcoarse
  have h2 := exponential_family_error hq
    (Nat.cast_nonneg (smallSets m hi).card) (smallSets_card_bound m hi hB hhi) hc hρ hfine
  have h3 := exponential_family_error hq
    (Nat.cast_nonneg (activeSizeBand m lo hi).card) (activeSizeBand_card_bound m lo hi hB hhi)
    hc hρ hrank
  have h1mul := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (N + 1))
  have h2mul := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (N + 1))
  unfold exceptionalBound
  simp only [neg_mul, mul_neg, mul_comm] at h1mul h2mul h3 ⊢
  nlinarith

theorem pow_exp_error_tendsto (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ d * Real.exp (-c * m)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast, neg_mul] using h

theorem polynomial_error_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (2 * (m : ℝ) ^ 3 + 3 * m) * Real.exp (-c * m)) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul (pow_exp_error_tendsto 3 hc)).add
    ((tendsto_const_nhds (x := (3 : ℝ))).mul (pow_exp_error_tendsto 1 hc))
  simpa only [add_mul, mul_assoc, pow_one, mul_zero, zero_add] using h

end ProbabilisticSerial.LowerBoundErrors
