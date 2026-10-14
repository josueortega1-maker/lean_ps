import LowerBoundCutoffs

/-! Every exponential band has an asymptotically full quota of expected cost. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundBandErrors
open CouponLowerBound ReplicaBandLower RawSurvivorBound LowerBoundErrors LowerBoundCutoffs

def coarseRate : ℝ := 3 - Real.log 4 - Real.log 2

lemma coarseRate_pos : 0 < coarseRate := coarse_rate_pos

def bandError (m q : ℕ) : ℝ :=
  6 * q / couponScale m + 2 * q * m * Real.exp (-coarseRate * m)

theorem bandError_tendsto (q : ℕ) : Tendsto (fun m => bandError m q) atTop (𝓝 0) := by
  have h1 := (tendsto_const_nhds (x := (6 : ℝ) * q)).mul
    (tendsto_inv_atTop_zero.comp couponScale_tendsto)
  have h2 := (tendsto_const_nhds (x := (2 : ℝ) * q)).mul
    (pow_exp_error_tendsto 1 coarseRate_pos)
  simpa only [bandError, div_eq_mul_inv, pow_one, mul_assoc, mul_zero, zero_add] using h1.add h2

theorem bandLowerValue_ge {m q : ℕ} (hm : 2 ≤ m) (hq : 0 < q)
    {D x : ℝ} (hD : 4 ≤ D) (hx : 0 ≤ x) (hupper : x ≤ Real.log m / 10) :
    (q : ℝ) - 32 * q ^ 2 / D - bandError m q ≤
      bandLowerValue m q (rawCutoff m x) (rawCutoff m (D * Real.exp x))
        (survivorCutoff m q (rawCutoff m (D * Real.exp x))) 4 := by
  let k := rawCutoff m x
  let s := survivorCutoff m q (rawCutoff m (D * Real.exp x))
  let μ := meanUnseen m k
  let F : ℝ := (survivorFamily m s).card
  let E : ℝ := Real.exp (-coarseRate * m)
  have hμ : 0 < μ := meanUnseen_pos hm k
  have hμbase : (m : ℝ) * Real.exp (-x) ≤ μ := mean_at_rawCutoff_ge hm hx
  have hμscale : couponScale m ≤ μ := couponScale_le_mean hm hx hupper
  have hscale : 1 ≤ couponScale m := couponScale_ge_one (by omega)
  have hμ1 : 1 ≤ μ := hscale.trans hμscale
  have hDpos : 0 < D := by linarith
  have hsc := survivorCutoff_le (q := q) hm hD hx
  change (s : ℝ) ≤ _ at hsc
  have hidentity : (q : ℝ) * (16 * (m * q : ℕ) / (D * Real.exp x)) =
      (16 * q ^ 2 / D) * ((m : ℝ) * Real.exp (-x)) := by
    rw [Nat.cast_mul, Real.exp_neg]
    field_simp
    <;> ring
  have hquota : (q : ℝ) * s ≤ (16 * q ^ 2 / D) * μ + q := by
    have h1 := mul_le_mul_of_nonneg_left hsc (Nat.cast_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left hμbase (show 0 ≤ 16 * (q : ℝ) ^ 2 / D by positivity)
    rw [← hidentity] at h2
    nlinarith
  have hcard : F ≤ Real.exp (Real.log 2 * m) := by
    have hc : (survivorFamily m s).card ≤ 2 ^ m := by
      simpa using (survivorFamily m s).card_le_univ
    have hcR : F ≤ (2 : ℝ) ^ m := by
      dsimp [F]
      exact_mod_cast hc
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hcR
  have hf := exponential_family_error hq (Nat.cast_nonneg (survivorFamily m s).card) hcard
    coarseRate_pos.le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    (show coarseRate + Real.log 2 ≤ 3 - Real.log 4 by unfold coarseRate; linarith)
  have hfailure : (q : ℝ) * m * F * Real.exp (-(3 - Real.log 4) * (m * q : ℕ)) ≤ q * m * E := by
    have h := mul_le_mul_of_nonneg_left hf (show 0 ≤ (q : ℝ) * m by positivity)
    simpa only [mul_assoc] using h
  let V := bandLowerValue m q k (rawCutoff m (D * Real.exp x)) s 4
  have hV : V * μ = (q : ℝ) * μ - 4 * q -
      2 * (q * (s : ℝ) + q * m * F * Real.exp (-(3 - Real.log 4) * (m * q : ℕ))) := by
    unfold V bandLowerValue
    change ((q : ℝ) * (1 - 4 / μ) -
      (q * (s : ℝ) + q * m * F * Real.exp (-(4 - 1 - Real.log 4) * (m * q : ℕ))) / (μ / 2)) * μ = _
    norm_num only
    field_simp
    <;> ring
  have hEpos : 0 ≤ (q : ℝ) * m * E := by dsimp [E]; positivity
  have hfailmul := mul_le_mul_of_nonneg_left hμ1 hEpos
  have hmain : (q : ℝ) - 32 * q ^ 2 / D - 6 * q / μ - 2 * q * m * E ≤ V := by
    apply (mul_le_mul_iff_of_pos_right hμ).mp
    rw [hV]
    have hcancel : (6 * (q : ℝ) / μ) * μ = 6 * q := div_mul_cancel₀ _ hμ.ne'
    have hconstant : 32 * (q : ℝ) ^ 2 / D = 2 * (16 * q ^ 2 / D) := by ring
    rw [hconstant]
    nlinarith
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 6 * (q : ℝ) by positivity)
    (by linarith : 0 < couponScale m) hμscale
  change (q : ℝ) - 32 * q ^ 2 / D - (6 * q / couponScale m + 2 * q * m * E) ≤ V
  linarith

end ProbabilisticSerial.LowerBoundBandErrors
