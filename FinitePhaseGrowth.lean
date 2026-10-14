import FinitePhaseConstants
import StandardLogStar

/-!
# The finite-expectation phase scales

The recurrence is written in the rescaled coordinate `x = c * lambda`.
All scales are concrete real sequences. The growing lower bound and the
one-step exponential growth are proved, rather than imposed as hypotheses.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FinitePhaseGrowth

open FinitePhaseConstants PhaseIntegral StandardLogStar

def z (j : ℕ) : ℝ := (5 / 6) / 2 ^ j
def c (j : ℕ) : ℝ := remainder (z j)

def x : ℕ → ℝ
  | 0 => Real.exp 1
  | j + 1 => c (j + 1) / c j * Real.exp 1 * z j * x j * Real.exp (x j)

def u (j : ℕ) : ℝ := c j / x j
def phaseTime (j : ℕ) : ℝ := 1 - u j
def theta (j : ℕ) : ℝ := z j * x j / c j

lemma z_pos (j : ℕ) : 0 < z j := by unfold z; positivity

lemma z_le_initial (j : ℕ) : z j ≤ 5 / 6 := by
  have h : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  unfold z
  exact div_le_self (by norm_num) h

@[simp] lemma z_zero : z 0 = 5 / 6 := by simp [z]

lemma z_succ (j : ℕ) : z (j + 1) = z j / 2 := by
  simp only [z, pow_succ]
  ring

lemma c_pos (j : ℕ) : 0 < c j := remainder_pos (z_pos j)

lemma remainder_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    remainder a ≤ remainder b := by
  have hea : 1 ≤ Real.exp a := by simpa using Real.exp_le_exp.mpr ha
  have hstep := Real.add_one_le_exp (b - a)
  have hmul := mul_le_mul_of_nonneg_left hstep (Real.exp_pos a).le
  have hprod := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hea)
  have heq : Real.exp a * Real.exp (b - a) = Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  dsimp [remainder]
  nlinarith

lemma c_le_initial (j : ℕ) : c j ≤ remainder (5 / 6) :=
  remainder_mono (z_pos j).le (z_le_initial j)

lemma c_ratio_lower (j : ℕ) :
    (1 / 4 : ℝ) * Real.exp (-5 / 12) ≤ c (j + 1) / c j := by
  have harg : (-5 / 12 : ℝ) ≤ -z j / 2 := by linarith [z_le_initial j]
  calc
    _ ≤ (1 / 4 : ℝ) * Real.exp (-z j / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
    _ ≤ c (j + 1) / c j := by
      simpa only [c, z_succ] using remainder_half_ratio (z_pos j)

lemma z_mul_lower {j : ℕ} (hj : Real.exp 1 * 2 ^ j ≤ x j) :
    5 * Real.exp 1 / 6 ≤ z j * x j := by
  have h := mul_le_mul_of_nonneg_left hj (z_pos j).le
  have hid : z j * (Real.exp 1 * 2 ^ j) = 5 * Real.exp 1 / 6 := by
    unfold z
    field_simp
    <;> ring
  rwa [hid] at h

lemma step_ge_exp_of_lower {j : ℕ} (hj : Real.exp 1 * 2 ^ j ≤ x j) :
    Real.exp (x j) ≤ x (j + 1) := by
  have hr := c_ratio_lower j
  have hz := z_mul_lower hj
  have he := (Real.exp_pos (1 : ℝ)).le
  have hratio : 0 ≤ c (j + 1) / c j := (div_pos (c_pos _) (c_pos _)).le
  have hcoeff : 1 ≤ c (j + 1) / c j * Real.exp 1 * (z j * x j) := by
    calc
      (1 : ℝ) ≤ (5 / 24) * Real.exp (19 / 12) := tower_multiplier_ge_one
      _ = ((1 / 4 : ℝ) * Real.exp (-5 / 12) * Real.exp 1) *
          (5 * Real.exp 1 / 6) := by
        have hid : Real.exp (19 / 12) =
            Real.exp (-5 / 12) * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hid]
        ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hr he) hz (by positivity)
        (mul_nonneg hratio he)
  have h := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (x j)).le
  simpa only [one_mul, x, mul_assoc] using h

lemma exp_ge_two_mul {a : ℝ} (ha : 0 ≤ a) : 2 * a ≤ Real.exp a := by
  nlinarith [Real.quadratic_le_exp_of_nonneg ha, sq_nonneg (a - 1)]

theorem x_ge_geometric : ∀ j, Real.exp 1 * 2 ^ j ≤ x j := by
  intro j
  induction j with
  | zero => simp [x]
  | succ j ih =>
      have hx : 0 ≤ x j := le_trans (by positivity) ih
      calc
        Real.exp 1 * 2 ^ (j + 1) = 2 * (Real.exp 1 * 2 ^ j) := by rw [pow_succ]; ring
        _ ≤ 2 * x j := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ Real.exp (x j) := exp_ge_two_mul hx
        _ ≤ x (j + 1) := step_ge_exp_of_lower ih

theorem x_step (j : ℕ) : Real.exp (x j) ≤ x (j + 1) :=
  step_ge_exp_of_lower (x_ge_geometric j)

lemma x_pos (j : ℕ) : 0 < x j :=
  lt_of_lt_of_le (by positivity) (x_ge_geometric j)

lemma u_pos (j : ℕ) : 0 < u j := div_pos (c_pos j) (x_pos j)

lemma theta_pos (j : ℕ) : 0 < theta j := div_pos (mul_pos (z_pos j) (x_pos j)) (c_pos j)

theorem x_ge_tower : ∀ j, iteratedExp 1 (j + 1) ≤ x j := by
  intro j
  induction j with
  | zero => simp [iteratedExp, x]
  | succ j ih =>
      exact (Real.exp_le_exp.mpr ih).trans (x_step j)

lemma exists_reach (m : ℕ) : ∃ j, Real.log (m : ℝ) ≤ x j := by
  obtain ⟨j, hj⟩ := exists_iteratedExp_ge 1 (Real.log (m : ℝ))
  refine ⟨j, hj.trans (?_ : iteratedExp 1 j ≤ x j)⟩
  have h : iteratedExp 1 j ≤ iteratedExp 1 (j + 1) := by
    rw [iteratedExp_succ]
    linarith [Real.add_one_le_exp (iteratedExp 1 j)]
  exact h.trans (x_ge_tower j)

def stoppingIndex (m : ℕ) : ℕ := Nat.find (exists_reach m)

theorem stoppingIndex_spec (m : ℕ) : Real.log (m : ℝ) ≤ x (stoppingIndex m) :=
  Nat.find_spec (exists_reach m)

lemma logStar_ge_two {m : ℕ} (hm : 3 ≤ m) : 2 ≤ logStar m := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hupper := cast_le_iteratedExp_logStar m
  by_contra hnot
  have hcases : logStar m = 0 ∨ logStar m = 1 := by omega
  rcases hcases with hk | hk
  · rw [hk] at hupper
    simp only [iteratedExp_zero] at hupper
    linarith
  · rw [hk] at hupper
    simp only [iteratedExp_succ, iteratedExp_zero] at hupper
    linarith [exp_one_bounds.2]

theorem stopping_phase_count {m : ℕ} (hm : 3 ≤ m) :
    stoppingIndex m + 1 ≤ logStar m - 1 := by
  have hk := logStar_ge_two hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log (m : ℝ) ≤ iteratedExp 1 (logStar m - 1) := by
    apply (Real.log_le_iff_le_exp hmpos).2
    rw [← iteratedExp_succ, Nat.sub_add_cancel (by omega : 1 ≤ logStar m)]
    exact cast_le_iteratedExp_logStar m
  have hreach : Real.log (m : ℝ) ≤ x (logStar m - 2) := by
    have ht := x_ge_tower (logStar m - 2)
    rw [show logStar m - 2 + 1 = logStar m - 1 by omega] at ht
    exact hlog.trans ht
  have hmin : stoppingIndex m ≤ logStar m - 2 := Nat.find_min' (exists_reach m) hreach
  omega

theorem endpoint_exposure_cost (m : ℕ) :
    u (stoppingIndex m) * Real.log (m : ℝ) ≤ c (stoppingIndex m) := by
  have h := mul_le_mul_of_nonneg_left (stoppingIndex_spec m) (u_pos (stoppingIndex m)).le
  have heq : u (stoppingIndex m) * x (stoppingIndex m) = c (stoppingIndex m) := by
    unfold u
    exact div_mul_cancel₀ _ (x_pos _).ne'
  rwa [heq] at h

theorem theta_gt_one (j : ℕ) : 1 < theta j := by
  have hbase := initial_parameter_gt_one
  have hc0 : 0 < remainder (5 / 6) := remainder_pos (by norm_num)
  have hnum := z_mul_lower (x_ge_geometric j)
  have hc := c_le_initial j
  have hbase' : 6 * remainder (5 / 6) < 5 * Real.exp 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 6 * remainder (5 / 6))).mp hbase
    simpa using h
  unfold theta
  apply (lt_div_iff₀ (c_pos j)).2
  nlinarith

lemma u_step (j : ℕ) :
    u (j + 1) = u j / (Real.exp 1 * z j * Real.exp (x j)) := by
  unfold u
  rw [x]
  have hc0 := c_pos j
  have hc1 := c_pos (j + 1)
  have hx := x_pos j
  have hz := z_pos j
  rw [div_div]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  field_simp [hc0.ne']
  <;> ring

theorem u_strict_step (j : ℕ) : u (j + 1) < u j := by
  have hnum := z_mul_lower (x_ge_geometric j)
  have hex : x j ≤ Real.exp (x j) := by linarith [Real.add_one_le_exp (x j)]
  have hp := mul_le_mul_of_nonneg_left hex (z_pos j).le
  have he := exp_one_bounds.1
  have hden : 1 < Real.exp 1 * z j * Real.exp (x j) := by
    have hmul := mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le
    have hlower := mul_le_mul_of_nonneg_left hnum (Real.exp_pos 1).le
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  rw [u_step]
  exact div_lt_self (u_pos j) hden

lemma u_antitone : Antitone u := antitone_nat_of_succ_le (fun j => (u_strict_step j).le)

@[simp] lemma phaseTime_zero : phaseTime 0 = initialTime := by
  simp [phaseTime, u, c, z, x, initialTime]

theorem phaseTime_bounds (j : ℕ) : 0 < phaseTime j ∧ phaseTime j < 1 := by
  have hu := u_pos j
  have hstart := initialTime_bounds.1
  have hmono := u_antitone (Nat.zero_le j)
  have hzero : phaseTime 0 = initialTime := phaseTime_zero
  dsimp [phaseTime] at hzero ⊢
  constructor <;> linarith

theorem phaseTime_strict_step (j : ℕ) : phaseTime j < phaseTime (j + 1) := by
  dsimp [phaseTime]
  linarith [u_strict_step j]

theorem theta_mul_next_u (j : ℕ) : theta j * u (j + 1) = Real.exp (-1 - x j) := by
  rw [u_step]
  have heq : Real.exp (-1 - x j) = 1 / (Real.exp 1 * Real.exp (x j)) := by
    rw [show -1 - x j = -(1 + x j) by ring, Real.exp_neg, Real.exp_add, one_div]
  rw [heq]
  unfold theta u
  field_simp [(c_pos j).ne', (x_pos j).ne', (z_pos j).ne', Real.exp_ne_zero]
  <;> ring

theorem phi_at_next_phase (j : ℕ) :
    FiniteExposure.phi (theta j) (u (j + 1)) = theta j + x j := by
  have ht := theta_gt_one j
  have hu := u_pos (j + 1)
  have hprod := theta_mul_next_u j
  have hex : Real.exp (-1 - x j) < 1 := Real.exp_lt_one_iff.mpr (by linarith [x_pos j])
  have hmid : theta j ≤ 1 / u (j + 1) := (le_div_iff₀ hu).2 (by linarith)
  unfold FiniteExposure.phi
  rw [if_neg (not_le_of_gt ht), if_pos hmid]
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (theta_pos j).ne' hu.ne', Real.log_exp] at hlog
  linarith

theorem unit_phase_cost {a : ℝ} (ha : 0 < a) :
    (a + remainder a) / (1 - Real.exp (-a)) = Real.exp a := by
  have hd : 1 - Real.exp (-a) ≠ 0 := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
    linarith
  apply (div_eq_iff hd).2
  dsimp [remainder]
  rw [Real.exp_neg]
  field_simp
  <;> ring

end ProbabilisticSerial.FinitePhaseGrowth
