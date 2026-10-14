import PhaseAdapter
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Asymptotic closure for Theorem 1

This file proves the two analytic facts used in the last paragraph of the
paper.  The exponential hitting time produced by the concrete phase argument
is negligible relative to `log n`, and Knuth's explicit harmonic expression
for random priority is asymptotic to `log n`.
-/

noncomputable section

open Filter
open scoped Topology
open Asymptotics

namespace ProbabilisticSerial.AsymptoticClosure

open PhaseIntegral PhaseAdapter LoadBound

/-! ## The concrete phase counter is `o(log n)` -/

/-- Iterated exponentiation grows at least geometrically. -/
lemma pow_two_mul_le_iteratedExp (u₀ : ℝ) :
    ∀ k : ℕ, (2 : ℝ) ^ k * u₀ ≤ iteratedExp u₀ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (2 : ℝ) ^ (k + 1) * u₀ = 2 * ((2 : ℝ) ^ k * u₀) := by ring
        _ ≤ 2 * iteratedExp u₀ k := by nlinarith
        _ ≤ Real.exp (iteratedExp u₀ k) := Real.two_mul_le_exp
        _ = iteratedExp u₀ (k + 1) := rfl

/-- A quantitative ordinary-logarithm upper bound on the least exponential
iteration count.  This intentionally proves a weaker bound than `logStar`;
it is already sufficient for the little-o conclusion. -/
theorem exponentialHeight_lt_log_bound {u₀ target : ℝ}
    (hu₀ : 0 < u₀) :
    (exponentialHeight u₀ target : ℝ) <
      Real.log (max 1 (target / u₀)) / Real.log 2 + 1 := by
  let x : ℝ := Real.log (max 1 (target / u₀)) / Real.log 2
  let k : ℕ := ⌈x⌉₊
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmaxPos : 0 < max 1 (target / u₀) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hmaxOne : 1 ≤ max 1 (target / u₀) := le_max_left _ _
  have hx : 0 ≤ x := by
    exact div_nonneg (Real.log_nonneg hmaxOne) hlogTwo.le
  have hxk : x ≤ (k : ℝ) := by
    exact Nat.le_ceil x
  have hlogLe : Real.log (max 1 (target / u₀)) ≤
      (k : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hxk hlogTwo.le
    calc
      Real.log (max 1 (target / u₀)) = x * Real.log 2 := by
        dsimp [x]
        field_simp [hlogTwo.ne']
      _ ≤ (k : ℝ) * Real.log 2 := hmul
  have hmaxPow : max 1 (target / u₀) ≤ (2 : ℝ) ^ k := by
    calc
      max 1 (target / u₀) =
          Real.exp (Real.log (max 1 (target / u₀))) :=
        (Real.exp_log hmaxPos).symm
      _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hlogLe
      _ = (2 : ℝ) ^ k := Real.exp_nat_mul (Real.log 2) k |>.trans (by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)])
  have htargetRatio : target / u₀ ≤ (2 : ℝ) ^ k :=
    (le_max_right _ _).trans hmaxPow
  have htarget : target ≤ (2 : ℝ) ^ k * u₀ := by
    have := mul_le_mul_of_nonneg_right htargetRatio hu₀.le
    field_simp [hu₀.ne'] at this ⊢
    nlinarith
  have hreach : target ≤ iteratedExp u₀ k :=
    htarget.trans (pow_two_mul_le_iteratedExp u₀ k)
  have hheightNat : exponentialHeight u₀ target ≤ k :=
    Nat.find_min' (exists_iteratedExp_ge u₀ target) hreach
  have hheightReal : (exponentialHeight u₀ target : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hheightNat
  exact hheightReal.trans_lt (by
    simpa [k, x] using Nat.ceil_lt_add_one hx)

lemma phaseStartScale_pos :
    0 < alphaZero * phaseLambdaZero / 2 := by
  exact div_pos (mul_pos alphaZero_pos phaseLambdaZero_pos) (by norm_num)

lemma phaseStartScale_half_le :
    (1 / 2 : ℝ) ≤ alphaZero * phaseLambdaZero / 2 := by
  have hinv := (phaseLambdaZero_spec.2 phaseLambdaZero le_rfl).1
  have hscaled := mul_le_mul_of_nonneg_left hinv alphaZero_pos.le
  have hone : (1 : ℝ) ≤ alphaZero * phaseLambdaZero := by
    convert hscaled using 1 <;> field_simp [alphaZero_pos.ne']
  linarith

lemma psLogStar_lt_loglog_bound (n : ℕ)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    psLogStar n <
      Real.log (Real.log (n : ℝ)) / Real.log 2 + 1 := by
  let u₀ : ℝ := alphaZero * phaseLambdaZero / 2
  let target : ℝ := Real.log (n : ℝ) / 2
  have hu₀ : 0 < u₀ := by simpa [u₀] using phaseStartScale_pos
  have huHalf : (1 / 2 : ℝ) ≤ u₀ := by
    simpa [u₀] using phaseStartScale_half_le
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hratioLe : target / u₀ ≤ Real.log (n : ℝ) := by
    have huDouble : 1 ≤ 2 * u₀ := by linarith
    have hlogNonneg : 0 ≤ Real.log (n : ℝ) := hlog.trans' zero_le_one
    dsimp [target]
    apply (div_le_iff₀ hu₀).2
    nlinarith
  have hmaxLe : max 1 (target / u₀) ≤ Real.log (n : ℝ) :=
    max_le hlog hratioLe
  have hmaxPos : 0 < max 1 (target / u₀) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlogLogPos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hlogMono : Real.log (max 1 (target / u₀)) ≤
      Real.log (Real.log (n : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hmaxPos hlogLogPos hmaxLe
  have hdivMono := div_le_div_of_nonneg_right hlogMono hlogTwo.le
  have hheight : psLogStar n <
      Real.log (max 1 (target / u₀)) / Real.log 2 + 1 := by
    simpa [psLogStar, u₀, target] using
      exponentialHeight_lt_log_bound (target := target) hu₀
  exact hheight.trans_le (add_le_add_right hdivMono 1)

lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_div_log_nat_zero :
    Tendsto
      (fun n : ℕ => Real.log (Real.log (n : ℝ)) /
        Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hsmall :
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[atTop]
        (fun n : ℕ => Real.log (n : ℝ)) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_nat_atTop
  exact hsmall.tendsto_div_nhds_zero

lemma tendsto_inv_log_nat_zero :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop

lemma tendsto_loglog_upper_ratio_zero :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Real.log (n : ℝ)) / Real.log 2 + 2) /
          Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlogTwoNe : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hfirst : Tendsto
      (fun n : ℕ =>
        (1 / Real.log 2) *
          (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_loglog_div_log_nat_zero
  have hsecond : Tendsto
      (fun n : ℕ => 2 * (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_inv_log_nat_zero
  have hsum := hfirst.add hsecond
  simpa only [zero_add] using hsum.congr' (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hlogn : Real.log (n : ℝ) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast hn
    field_simp [hlogTwoNe, hlogn]
    <;> ring)

/-- The exact shifted exponential-height counter generated by Step 9 is
little-o of the logarithmic RP scale. -/
theorem psLogStar_small_relative_to_log :
    (fun n : ℕ => 1 + psLogStar n) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ)))
      tendsto_loglog_upper_ratio_zero
    filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hlog
    have hlogPos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
    exact div_nonneg (by linarith [psLogStar_nonneg n]) hlogPos.le
    filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hlog
    have hlogPos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
    apply (div_le_div_iff₀ hlogPos hlogPos).2
    have hstar := psLogStar_lt_loglog_bound n hlog
    nlinarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn hzero
    have hlogPos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hn
    exact (hlogPos.ne' hzero).elim

/-! ## Knuth's random-priority benchmark -/

/-- The exact expectation from Knuth's lemma. -/
def rpExpectation (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / n * ((harmonic (n + 1) : ℝ) - 1)

theorem harmonic_isEquivalent_log :
    (fun n : ℕ => (harmonic n : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · have hdiff := Real.tendsto_harmonic_sub_log
    have hratioDiff : Tendsto
        (fun n : ℕ =>
          (((harmonic n : ℝ) - Real.log (n : ℝ)) /
            Real.log (n : ℝ))) atTop (𝓝 0) := by
      exact hdiff.div_atTop tendsto_log_nat_atTop
    have hadd := hratioDiff.add_const 1
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      have hlogn : Real.log (n : ℝ) ≠ 0 := by
        apply (Real.log_pos ?_).ne'
        exact_mod_cast hn
      simp only [Pi.div_apply]
      field_simp [hlogn]
      <;> ring)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    apply (Real.log_pos ?_).ne'
    exact_mod_cast hn

/-- Knuth's exact harmonic expression is asymptotic to `log n`. -/
theorem rpExpectation_isEquivalent_log :
    rpExpectation ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hharmShift := Real.tendsto_harmonic_sub_log.comp hshift
    have hlogShift := Real.tendsto_log_nat_add_one_sub_log
    have hdiff : Tendsto
        (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log (n : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) := by
      have hadd := hharmShift.add hlogShift
      simpa only [add_zero] using hadd.congr' (by
        filter_upwards with n
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one,
          Nat.add_comm]
        ring)
    have hdiffOne : Tendsto
        (fun n : ℕ =>
          ((harmonic (n + 1) : ℝ) - Real.log (n : ℝ)) - 1)
        atTop (𝓝 (Real.eulerMascheroniConstant - 1)) := by
      simpa using hdiff.sub tendsto_const_nhds
    have hratioDiff : Tendsto
        (fun n : ℕ =>
          (((harmonic (n + 1) : ℝ) - Real.log (n : ℝ)) - 1) /
            Real.log (n : ℝ)) atTop (𝓝 0) :=
      hdiffOne.div_atTop tendsto_log_nat_atTop
    have hbRatio : Tendsto
        (fun n : ℕ =>
          ((harmonic (n + 1) : ℝ) - 1) / Real.log (n : ℝ))
        atTop (𝓝 1) := by
      have hadd := hratioDiff.add_const 1
      simpa only [zero_add] using hadd.congr' (by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
        have hlogn : Real.log (n : ℝ) ≠ 0 := by
          apply (Real.log_pos ?_).ne'
          exact_mod_cast hn
        field_simp [hlogn]
        <;> ring)
    have hfactor : Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      have hadd := hone.add tendsto_inverse_atTop_nhds_zero_nat
      simpa only [add_zero] using hadd.congr' (by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        push_cast
        field_simp [hn0]
        <;> ring)
    have hproduct := hfactor.mul hbRatio
    simpa only [one_mul] using hproduct.congr' (by
      filter_upwards with n
      simp only [Pi.div_apply, rpExpectation]
      ring)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    apply (Real.log_pos ?_).ne'
    exact_mod_cast hn

end ProbabilisticSerial.AsymptoticClosure
