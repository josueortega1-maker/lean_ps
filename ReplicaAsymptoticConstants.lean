import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Replica tail arithmetic and critical-regime separation

These prove the market-size conversion in the tail bound and the strict
separation of the limiting RP root from the PS quadratic bound. They do not
construct the replica RP mechanism or establish its asymptotics.
-/

noncomputable section

namespace ProbabilisticSerial.ReplicaAsymptoticConstants

lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      omega

lemma quota_cube_le_power {m q : ℕ} (hm : 2 ≤ m) (hq : 0 < q) :
    q ^ 3 ≤ m ^ (8 * (q - 1)) := by
  have hqpow : q ≤ 2 ^ (q - 1) := by
    have h := succ_le_two_pow (q - 1)
    simpa only [Nat.sub_add_cancel hq] using h
  calc
    q ^ 3 ≤ (2 ^ (q - 1)) ^ 3 := Nat.pow_le_pow_left hqpow 3
    _ = 2 ^ (3 * (q - 1)) := by rw [← pow_mul, Nat.mul_comm (q - 1) 3]
    _ ≤ 2 ^ (8 * (q - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ m ^ (8 * (q - 1)) := Nat.pow_le_pow_left hm _

/-- The paper's `m^(5-8q)` failure estimate is at most `1/(m*q)^3`. -/
theorem polynomial_failure_le_agents_cube {m q : ℕ} (hm : 2 ≤ m) (hq : 0 < q) :
    (m : ℝ) ^ 5 / (m : ℝ) ^ (8 * q) ≤ 1 / ((m : ℝ) * q) ^ 3 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcube : (q : ℝ) ^ 3 ≤ (m : ℝ) ^ (8 * (q - 1)) := by
    exact_mod_cast quota_cube_le_power hm hq
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [one_mul]
  calc
    (m : ℝ) ^ 5 * ((m : ℝ) * q) ^ 3 = (m : ℝ) ^ 8 * (q : ℝ) ^ 3 := by ring
    _ ≤ (m : ℝ) ^ 8 * (m : ℝ) ^ (8 * (q - 1)) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (m : ℝ) ^ (8 * q) := by rw [← pow_add]; congr 1; omega

def rate (r : ℝ) : ℝ := r - 1 - Real.log r

theorem rate_one_add_lt_quadratic {s : ℝ} (hs : 0 < s) :
    rate (1 + s) < s ^ 2 / 2 := by
  have hlog := Real.lt_log_one_add_of_pos hs
  have hpoly : s - s ^ 2 / 2 < 2 * s / (s + 2) := by
    apply (lt_div_iff₀ (by linarith : 0 < s + 2)).2
    nlinarith [pow_pos hs 3]
  unfold rate
  linarith

lemma rate_monotone {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : rate a ≤ rate b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have hdiv : b / a - 1 ≤ b - a := by
    have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hab)
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ ha0).2
    nlinarith
  unfold rate
  linarith

/-- The limiting RP root is strictly above the PS critical-regime bound. -/
theorem critical_root_separation {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    (hroot : rate r = 1 / c) :
    1 + Real.sqrt (2 / c) < r := by
  have hs : 0 < Real.sqrt (2 / c) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 / c by positivity)
  have hstrict := rate_one_add_lt_quadratic hs
  rw [hsq] at hstrict
  rw [show (2 / c : ℝ) / 2 = 1 / c by ring] at hstrict
  by_contra hnot
  have hmono := rate_monotone hr.le (le_of_not_gt hnot)
  rw [hroot] at hmono
  linarith

end ProbabilisticSerial.ReplicaAsymptoticConstants
