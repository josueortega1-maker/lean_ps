import FinitePhaseGrowth
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite phase summation and the additive constant

The excess is bounded on every finite prefix. Convexity bounds the geometric
tail after the first two terms; no exchange of infinite sums is needed.
The final assembly takes explicit phase-increment inequalities for a function
`f`. The probabilistic exposure argument must provide those inequalities.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FinitePhaseSum

open FinitePhaseConstants FinitePhaseGrowth StandardLogStar

lemma exp_scaled_excess {a t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t * a) - 1 ≤ t * (Real.exp a - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ a)
    (show 0 ≤ 1 - t by linarith) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  linarith

lemma geometric_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j) = 2 * (1 - (1 / 2 : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma tail_excess_sum_le (k : ℕ) :
    (∑ j ∈ Finset.range k, (Real.exp (z (j + 2)) - 1)) ≤
      2 * (Real.exp (5 / 24) - 1) := by
  have he : 0 ≤ Real.exp (5 / 24) - 1 := by
    have h := Real.add_one_le_exp (5 / 24 : ℝ)
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j * (Real.exp (5 / 24) - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hz : z (j + 2) = (1 / 2 : ℝ) ^ j * (5 / 24) := by
        simp only [z, pow_add, div_pow, one_pow]
        norm_num
        ring
      rw [hz]
      exact exp_scaled_excess (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    _ = (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j) * (Real.exp (5 / 24) - 1) := by
      rw [Finset.sum_mul]
    _ ≤ 2 * (Real.exp (5 / 24) - 1) := by
      apply mul_le_mul_of_nonneg_right _ he
      rw [geometric_sum]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

lemma exp_five_twelfths_upper : Real.exp (5 / 12) ≤ (1516897 / 1000000 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 5 / 12)
    (by norm_num : (5 / 12 : ℝ) ≤ 1) (by norm_num : 0 < (12 : ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_five_twentyfourths_upper : Real.exp (5 / 24) ≤ (1231624 / 1000000 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 5 / 24)
    (by norm_num : (5 / 24 : ℝ) ≤ 1) (by norm_num : 0 < (12 : ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem phase_excess_sum_lt (N : ℕ) :
    (∑ j ∈ Finset.range N, (Real.exp (z j) - 1)) < (2291 / 1000 : ℝ) := by
  rcases N with _ | N
  · norm_num
  rcases N with _ | k
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, z_zero]
    linarith [exp_five_sixths_bounds.2]
  have hsplit :
      (∑ j ∈ Finset.range (k + 1 + 1), (Real.exp (z j) - 1)) =
        (Real.exp (5 / 6) - 1) + (Real.exp (5 / 12) - 1) +
          ∑ j ∈ Finset.range k, (Real.exp (z (j + 2)) - 1) := by
    rw [show k + 1 + 1 = 2 + k by omega, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, z, Nat.add_comm]
    <;> ring
  rw [hsplit]
  linarith [tail_excess_sum_le k, exp_five_sixths_bounds.2,
    exp_five_twelfths_upper, exp_five_twentyfourths_upper]

/-- Analytic assembly at the concrete stopping index. No expectation or
mechanism is defined by the bound: a later application must prove the initial,
phase and terminal estimates for the actual expected exposure. -/
theorem phase_assembly (f : ℝ → ℝ) (m : ℕ) (hm : 3 ≤ m)
    (hinitial : f (phaseTime 0) ≤ envelope initialTime)
    (hphase : ∀ j, f (phaseTime (j + 1)) - f (phaseTime j) ≤ Real.exp (z j))
    (hterminal : f 1 - f (phaseTime (stoppingIndex m)) ≤ Real.exp (z (stoppingIndex m))) :
    f 1 < (logStar m : ℝ) + 17 / 5 := by
  have hprefix : ∀ k, f (phaseTime k) ≤ f (phaseTime 0) +
      ∑ j ∈ Finset.range k, Real.exp (z j) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        linarith [hphase k]
  have htotal : f 1 ≤ f (phaseTime 0) +
      ∑ j ∈ Finset.range (stoppingIndex m + 1), Real.exp (z j) := by
    rw [Finset.sum_range_succ]
    linarith [hprefix (stoppingIndex m)]
  have hsum : (∑ j ∈ Finset.range (stoppingIndex m + 1), Real.exp (z j)) =
      ((stoppingIndex m + 1 : ℕ) : ℝ) +
        ∑ j ∈ Finset.range (stoppingIndex m + 1), (Real.exp (z j) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsum] at htotal
  have hcount : ((stoppingIndex m + 1 : ℕ) : ℝ) ≤ (logStar m : ℝ) - 1 := by
    have h := stopping_phase_count hm
    have hk : 1 ≤ logStar m := by have := logStar_ge_two hm; omega
    have h' : ((stoppingIndex m + 1 : ℕ) : ℝ) ≤ ((logStar m - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa only [Nat.cast_sub hk, Nat.cast_one] using h'
  linarith [initial_envelope_lt, phase_excess_sum_lt (stoppingIndex m + 1)]

end ProbabilisticSerial.FinitePhaseSum
