import FinitePhaseSum

/-!+# Analytic closure for a finite exposure trace

An expected exposure is a positive finite sum of ramps. This representation
allows the phase estimates to be proved directly from exponential arrival
costs, without exchanging integrals and expectations. The hypotheses on those
costs remain explicit: applying the result to PS requires the actual trace
and the probabilistic arrival bounds.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteAtomicExposure

open FinitePhaseGrowth FinitePhaseConstants FiniteExposure FinitePhaseSum StandardLogStar

def arrivalCost (θ r : ℝ) : ℝ := 1 - Real.exp (-θ * r)

lemma arrivalCost_nonneg {θ r : ℝ} (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    0 ≤ arrivalCost θ r := by
  have h : Real.exp (-θ * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact sub_nonneg.mpr h

lemma arrivalCost_pos {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) :
    0 < arrivalCost θ r := by
  have h : Real.exp (-θ * r) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact sub_pos.mpr h

lemma arrivalCost_mono {θ r s : ℝ} (hθ : 0 ≤ θ) (hrs : r ≤ s) :
    arrivalCost θ r ≤ arrivalCost θ s := by
  have h := Real.exp_le_exp.mpr (show -θ * s ≤ -θ * r by nlinarith)
  unfold arrivalCost
  linarith

/-- Concavity of the arrival cost, in a form that includes a truncated ramp. -/
lemma truncated_cost {θ d r b : ℝ} (hθ : 0 ≤ θ) (hd : 0 < d)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hbr : b ≤ r) (hbd : b ≤ d) :
    b * arrivalCost θ d ≤ d * arrivalCost θ r := by
  by_cases hrd : r ≤ d
  · have hscale : 0 ≤ r / d := div_nonneg hr hd.le
    have hscale1 : r / d ≤ 1 := (div_le_one hd).2 hrd
    have h := exp_scaled_excess (a := -θ * d) hscale hscale1
    have heq : r / d * (-θ * d) = -θ * r := by field_simp; ring
    rw [heq] at h
    have hc : r / d * arrivalCost θ d ≤ arrivalCost θ r := by
      unfold arrivalCost
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hc hd.le
    have hid : d * (r / d * arrivalCost θ d) = r * arrivalCost θ d := by
      field_simp
    rw [hid] at hmul
    exact (mul_le_mul_of_nonneg_right hbr (arrivalCost_nonneg hθ hd.le)).trans hmul
  · exact (mul_le_mul_of_nonneg_right hbd (arrivalCost_nonneg hθ hd.le)).trans
      (mul_le_mul_of_nonneg_left (arrivalCost_mono hθ (le_of_not_ge hrd)) hd.le)

lemma phase_factor_mono {θ d v : ℝ} (hθ : 0 < θ) (hd : 0 < d) (hdv : d ≤ v) :
    d / arrivalCost θ d ≤ v / arrivalCost θ v := by
  have hv : 0 < v := hd.trans_le hdv
  apply (div_le_div_iff₀ (arrivalCost_pos hθ hd) (arrivalCost_pos hθ hv)).2
  exact truncated_cost hθ.le hv hd.le hd.le le_rfl hdv

structure Data (ι : Type*) where
  weight : ι → ℝ
  time : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  time_nonneg : ∀ i, 0 ≤ time i

variable {ι : Type*} [Fintype ι]

def value (D : Data ι) (t : ℝ) : ℝ :=
  ∑ i, D.weight i * max (t - D.time i) 0

def cost (D : Data ι) (θ t : ℝ) : ℝ :=
  ∑ i, D.weight i * arrivalCost θ (max (t - D.time i) 0)

lemma value_zero (D : Data ι) : (value D) 0 = 0 := by
  unfold value
  apply Finset.sum_eq_zero
  intro i hi
  rw [max_eq_right (by linarith [D.time_nonneg i])]
  ring

lemma value_monotone (D : Data ι) : Monotone (value D) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (D.weight_nonneg i)

lemma increment_cost (D : Data ι) {s t θ : ℝ} (hst : s < t) (hθ : 0 < θ) :
    ((value D) t - (value D) s) * arrivalCost θ (t - s) ≤ (t - s) * (cost D) θ t := by
  have hatom : ∀ i, (max (t - D.time i) 0 - max (s - D.time i) 0) *
      arrivalCost θ (t - s) ≤ (t - s) * arrivalCost θ (max (t - D.time i) 0) := by
    intro i
    have hm : max (s - D.time i) 0 ≤ max (t - D.time i) 0 :=
      max_le_max (by linarith) le_rfl
    apply truncated_cost hθ.le (sub_pos.mpr hst) (le_max_right _ _) (sub_nonneg.mpr hm)
    · linarith [le_max_right (s - D.time i) (0 : ℝ)]
    · by_cases ht : 0 ≤ t - D.time i
      · rw [max_eq_left ht]
        linarith [le_max_left (s - D.time i) (0 : ℝ)]
      · rw [max_eq_right (le_of_not_ge ht)]
        linarith [le_max_right (s - D.time i) (0 : ℝ)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => mul_le_mul_of_nonneg_left (hatom i) (D.weight_nonneg i))
  simpa only [value, cost, Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.mul_sum, mul_sub, sub_mul, mul_assoc, mul_left_comm] using hsum

theorem increment_le (D : Data ι) {s t θ B : ℝ} (hst : s < t) (hθ : 0 < θ)
    (hcost : (cost D) θ t ≤ B) :
    (value D) t - (value D) s ≤ (t - s) * B / arrivalCost θ (t - s) := by
  apply (le_div_iff₀ (arrivalCost_pos hθ (sub_pos.mpr hst))).2
  exact (increment_cost D hst hθ).trans
    (mul_le_mul_of_nonneg_left hcost (sub_pos.mpr hst).le)

lemma theta_mul_u (j : ℕ) : theta j * u j = z j := by
  unfold theta u
  field_simp [(c_pos j).ne', (x_pos j).ne']

lemma u_mul_x (j : ℕ) : u j * x j = c j :=
  div_mul_cancel₀ _ (x_pos j).ne'

lemma initial_phi {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    phi (1 + t) (1 - t) = t - Real.log (1 - t ^ 2) := by
  have hsmall : ¬1 + t ≤ 1 := by linarith
  have hmiddle : 1 + t ≤ 1 / (1 - t) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - t)).2
    nlinarith [sq_nonneg t]
  rw [phi, if_neg hsmall, if_pos hmiddle,
    show 1 - t ^ 2 = (1 - t) * (1 + t) by ring,
    Real.log_mul (by linarith : 1 - t ≠ 0) (by linarith : 1 + t ≠ 0)]
  ring

theorem initial_envelope (D : Data ι) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hcost : (cost D) (1 + t) t ≤ phi (1 + t) (1 - t)) :
    (value D) t ≤ envelope t := by
  have h := increment_le D ht (by linarith : 0 < 1 + t) hcost
  rw [value_zero, sub_zero, sub_zero, initial_phi ht ht1] at h
  simpa only [envelope, arrivalCost, show -(1 + t) * t = -t - t ^ 2 by ring] using h

/-- Complete analytic phase argument for positive finite exposure traces.
The two probabilistic cost bounds, and the relation to expected rank, are
deliberately not hidden inside the definition of the trace. -/
theorem logarithmic_bound (D : Data ι) (m : ℕ) (hm : 3 ≤ m)
    (hinterior : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ →
      (cost D) θ t ≤ phi θ (1 - t))
    (hendpoint : ∀ θ, 0 < θ → (cost D) θ 1 ≤ θ + Real.log (m : ℝ)) :
    (value D) 1 < (logStar m : ℝ) + 17 / 5 := by
  apply phase_assembly (value D) m hm
  · rw [phaseTime_zero]
    exact initial_envelope D (by linarith [initialTime_bounds.1])
      (by linarith [initialTime_bounds.2])
      (hinterior _ (by linarith [initialTime_bounds.1])
        (by linarith [initialTime_bounds.2]) _ (by linarith [initialTime_bounds.1]))
  · intro j
    have hcost := hinterior _ (phaseTime_bounds (j + 1)).1
      (phaseTime_bounds (j + 1)).2 _ (theta_pos j)
    have harg : 1 - phaseTime (j + 1) = u (j + 1) := by unfold phaseTime; ring
    rw [harg, phi_at_next_phase] at hcost
    have h := increment_le D (phaseTime_strict_step j) (theta_pos j) hcost
    have hd : 0 < phaseTime (j + 1) - phaseTime j := sub_pos.mpr (phaseTime_strict_step j)
    have hdle : phaseTime (j + 1) - phaseTime j ≤ u j := by
      dsimp [phaseTime]
      linarith [u_pos (j + 1)]
    have hfactor := phase_factor_mono (theta_pos j) hd hdle
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (show 0 ≤ theta j + x j by linarith [theta_pos j, x_pos j])
    have hfinal : u j / arrivalCost (theta j) (u j) * (theta j + x j) = Real.exp (z j) := by
      rw [div_mul_eq_mul_div, mul_add, mul_comm (u j) (theta j), theta_mul_u, u_mul_x]
      change (z j + remainder (z j)) / (1 - Real.exp (-(theta j) * u j)) = _
      rw [neg_mul, theta_mul_u]
      exact unit_phase_cost (z_pos j)
    rw [hfinal] at hmul
    exact h.trans (by simpa only [div_mul_eq_mul_div] using hmul)
  · let j := stoppingIndex m
    have h := increment_le D (phaseTime_bounds j).2 (theta_pos j)
      (hendpoint _ (theta_pos j))
    have harg : 1 - phaseTime j = u j := by unfold phaseTime; ring
    rw [harg] at h
    have hnum : u j * (theta j + Real.log (m : ℝ)) ≤ z j + c j := by
      rw [mul_add, mul_comm (u j) (theta j), theta_mul_u]
      exact add_le_add_left (endpoint_exposure_cost m) _
    have hdiv := div_le_div_of_nonneg_right hnum (arrivalCost_pos (theta_pos j) (u_pos j)).le
    have hfinal : (z j + c j) / arrivalCost (theta j) (u j) = Real.exp (z j) := by
      unfold arrivalCost
      rw [neg_mul, theta_mul_u]
      exact unit_phase_cost (z_pos j)
    rw [hfinal] at hdiv
    exact h.trans hdiv

end ProbabilisticSerial.FiniteAtomicExposure
