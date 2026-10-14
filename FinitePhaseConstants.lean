import FiniteExposure

/-!
# Exact scalar bounds for the finite expectation phase argument

The exponential enclosures below follow from rational Taylor sums and the
proved remainder bound in mathlib. These are scalar parts of the analytic
`+3.4` argument; the exposure/rank bridge and phase summation remain separate
proof obligations. The 1920-point below-five certificate is a different task.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FinitePhaseConstants

def remainder (z : ℝ) : ℝ := Real.exp z - 1 - z

def initialTime : ℝ := 1 - remainder (5 / 6) / Real.exp 1

def envelope (s : ℝ) : ℝ :=
  s * (s - Real.log (1 - s ^ 2)) / (1 - Real.exp (-s - s ^ 2))

lemma remainder_pos {z : ℝ} (hz : 0 < z) : 0 < remainder z := by
  have h := Real.quadratic_le_exp_of_nonneg hz.le
  dsimp [remainder]
  nlinarith [sq_pos_of_pos hz]

/-- The phase-growth comparison can be proved directly from the quadratic
Taylor lower bound; an integral representation of the remainder is unnecessary. -/
theorem remainder_half_mul_exp {z : ℝ} (hz : 0 ≤ z) :
    remainder z ≤ 4 * Real.exp (z / 2) * remainder (z / 2) := by
  have heq : Real.exp z = (Real.exp (z / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hquad := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ z / 2)
  have hd : 0 ≤ Real.exp (z / 2) - 1 - z / 2 := by nlinarith
  have hprod := mul_nonneg (by linarith : 0 ≤ z / 2) hd
  dsimp [remainder]
  rw [heq]
  nlinarith [sq_nonneg (Real.exp (z / 2) - 1 - z / 2)]

theorem remainder_half_ratio {z : ℝ} (hz : 0 < z) :
    (1 / 4 : ℝ) * Real.exp (-z / 2) ≤ remainder (z / 2) / remainder z := by
  have he : 0 < Real.exp (z / 2) := Real.exp_pos _
  have hc : 0 < remainder z := remainder_pos hz
  rw [show (1 / 4 : ℝ) * Real.exp (-z / 2) = 1 / (4 * Real.exp (z / 2)) by
    rw [show -z / 2 = -(z / 2) by ring, Real.exp_neg]
    ring]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.exp (z / 2)) hc).2
  nlinarith [remainder_half_mul_exp hz.le]

lemma exp_five_sixths_bounds :
    (2300975 / 1000000 : ℝ) ≤ Real.exp (5 / 6) ∧
      Real.exp (5 / 6) ≤ (2300976 / 1000000 : ℝ) := by
  have hlo := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) 12
  have hhi := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 5 / 6)
    (by norm_num : (5 / 6 : ℝ) ≤ 1) (by norm_num : 0 < (12 : ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  constructor <;> linarith

lemma exp_one_bounds :
    (2718281 / 1000000 : ℝ) ≤ Real.exp 1 ∧
      Real.exp 1 ≤ (2718282 / 1000000 : ℝ) := by
  have hlo := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 12
  have hhi := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : 0 < (12 : ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  constructor <;> linarith

theorem tower_multiplier_ge_one :
    (1 : ℝ) ≤ (5 / 24) * Real.exp (19 / 12) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 12) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem initial_parameter_gt_one :
    1 < (5 * Real.exp 1) / (6 * remainder (5 / 6)) := by
  have hc : 0 < remainder (5 / 6) := by
    dsimp [remainder]
    linarith [exp_five_sixths_bounds.1]
  apply (lt_div_iff₀ (by positivity : 0 < 6 * remainder (5 / 6))).2
  dsimp [remainder]
  linarith [exp_five_sixths_bounds.2, exp_one_bounds.1]

theorem initialTime_bounds :
    (82796 / 100000 : ℝ) < initialTime ∧ initialTime < (82797 / 100000 : ℝ) := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hcUpper : remainder (5 / 6) / Real.exp 1 < 1 - (82796 / 100000 : ℝ) := by
    apply (div_lt_iff₀ he).2
    dsimp [remainder]
    linarith [exp_five_sixths_bounds.2, exp_one_bounds.1]
  have hcLower : 1 - (82797 / 100000 : ℝ) < remainder (5 / 6) / Real.exp 1 := by
    apply (lt_div_iff₀ he).2
    dsimp [remainder]
    linarith [exp_five_sixths_bounds.1, exp_one_bounds.2]
  dsimp [initialTime]
  constructor <;> linarith

theorem excess_scalar_lt :
    2 * (5 / 6 : ℝ) + (4 / 3) * remainder (5 / 6) < (2291 / 1000 : ℝ) := by
  dsimp [remainder]
  linarith [exp_five_sixths_bounds.2]

lemma exp_log_threshold : (31803 / 10000 : ℝ) < Real.exp (1157 / 1000) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1157 / 1000) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_denominator_threshold :
    (45424 / 10000 : ℝ) <
      Real.exp ((82796 / 100000 : ℝ) + (82796 / 100000 : ℝ) ^ 2) := by
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ (82796 / 100000 : ℝ) + (82796 / 100000 : ℝ) ^ 2) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem envelope_lt_on_initial_interval {s : ℝ}
    (hlo : (82796 / 100000 : ℝ) ≤ s) (hhi : s ≤ (82797 / 100000 : ℝ)) :
    envelope s < (2108 / 1000 : ℝ) := by
  have hs : 0 < s := by linarith
  have hu : 0 < 1 - s ^ 2 := by nlinarith
  have huLower : (1 : ℝ) - (82797 / 100000 : ℝ) ^ 2 ≤ 1 - s ^ 2 := by
    nlinarith
  have hlog : -Real.log (1 - s ^ 2) < (1157 / 1000 : ℝ) := by
    have hx : (1 : ℝ) / (1 - s ^ 2) < Real.exp (1157 / 1000) := by
      apply (div_lt_iff₀ hu).2
      calc
        (1 : ℝ) < (31803 / 10000 : ℝ) * (1 - (82797 / 100000 : ℝ) ^ 2) := by
          norm_num
        _ ≤ Real.exp (1157 / 1000) * (1 - s ^ 2) :=
          mul_le_mul exp_log_threshold.le huLower (by norm_num) (Real.exp_pos _).le
    have h := (Real.log_lt_iff_lt_exp (div_pos zero_lt_one hu)).2 hx
    simpa [Real.log_div, hu.ne'] using h
  have harg : (82796 / 100000 : ℝ) + (82796 / 100000 : ℝ) ^ 2 ≤ s + s ^ 2 := by
    nlinarith
  have he : (45424 / 10000 : ℝ) < Real.exp (s + s ^ 2) :=
    exp_denominator_threshold.trans_le (Real.exp_le_exp.mpr harg)
  have hinv : Real.exp (-s - s ^ 2) ≤ (22015 / 100000 : ℝ) := by
    rw [show -s - s ^ 2 = -(s + s ^ 2) by ring, Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith
  have hd : (77985 / 100000 : ℝ) ≤ 1 - Real.exp (-s - s ^ 2) := by linarith
  have hdpos : 0 < 1 - Real.exp (-s - s ^ 2) := by linarith
  unfold envelope
  apply (div_lt_iff₀ hdpos).2
  have hnum : s * (s - Real.log (1 - s ^ 2)) <
      (82797 / 100000 : ℝ) * ((82797 / 100000 : ℝ) + (1157 / 1000 : ℝ)) := by
    calc
      _ < s * (s + (1157 / 1000 : ℝ)) :=
        mul_lt_mul_of_pos_left (by linarith) hs
      _ ≤ _ := by gcongr
  linarith

theorem initial_envelope_lt : envelope initialTime < (2108 / 1000 : ℝ) :=
  envelope_lt_on_initial_interval initialTime_bounds.1.le initialTime_bounds.2.le

/-- The exact arithmetic of the final additive slack, once the separate
phase-count and phase-sum arguments have been supplied. -/
theorem additive_slack_lt :
    (-1 : ℝ) + (2108 / 1000) + (2291 / 1000) < (17 / 5 : ℝ) := by norm_num

end ProbabilisticSerial.FinitePhaseConstants
