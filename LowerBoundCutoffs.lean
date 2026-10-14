import LowerBoundErrors
import LowerBoundBands

/-! Rounded raw-prefix cutoffs for the fixed-quota exponential bands. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundCutoffs
open CouponLowerBound LowerBoundBands

def rawCutoff (m : ℕ) (x : ℝ) : ℕ := ⌊(m : ℝ) * x / 2⌋₊

lemma rawCutoff_mono (m : ℕ) : Monotone (rawCutoff m) := by
  intro x y hxy
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg _)) (by norm_num)

lemma rawCutoff_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (rawCutoff m x : ℝ) ≤ m * x / 2 := Nat.floor_le (by positivity)

theorem mean_at_rawCutoff_ge {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    (m : ℝ) * Real.exp (-x) ≤ meanUnseen m (rawCutoff m x) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply le_trans _ (meanUnseen_ge_exponential hm (rawCutoff m x))
  apply mul_le_mul_of_nonneg_left _ hmR.le
  apply Real.exp_le_exp.mpr
  have hk := rawCutoff_le m hx
  have h : 2 * (rawCutoff m x : ℝ) / m ≤ x := (div_le_iff₀ hmR).2 (by linarith)
  linarith

def couponScale (m : ℕ) : ℝ := Real.exp (Real.log m / 2)

lemma couponScale_le_mean {m : ℕ} (hm : 2 ≤ m) {x : ℝ}
    (hx : 0 ≤ x) (hupper : x ≤ Real.log m / 10) :
    couponScale m ≤ meanUnseen m (rawCutoff m x) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have heq : couponScale m = (m : ℝ) * Real.exp (-Real.log m / 2) := by
    calc
      couponScale m = Real.exp (Real.log m + (-Real.log m / 2)) := by
        unfold couponScale
        congr 1
        ring
      _ = (m : ℝ) * Real.exp (-Real.log m / 2) := by
        rw [Real.exp_add, Real.exp_log hmR]
  rw [heq]
  apply le_trans _ (mean_at_rawCutoff_ge hm hx)
  apply mul_le_mul_of_nonneg_left _ hmR.le
  exact Real.exp_le_exp.mpr (by linarith)

lemma couponScale_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ couponScale m := by
  apply Real.one_le_exp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (by norm_num)

theorem couponScale_tendsto : Tendsto couponScale atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

def survivorCutoff (m q ending : ℕ) : ℕ := ⌈(4 : ℝ) * (m * q : ℕ) * m / ending⌉₊

lemma survivorCutoff_mean {m q ending : ℕ} (hm : 0 < m) (he : 0 < ending) :
    (4 : ℝ) * (m * q : ℕ) ≤ ending * ((survivorCutoff m q ending : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heR : (0 : ℝ) < ending := by exact_mod_cast he
  have h := Nat.le_ceil ((4 : ℝ) * (m * q : ℕ) * m / ending)
  change _ ≤ (survivorCutoff m q ending : ℝ) at h
  have hmul := (div_le_iff₀ heR).1 h
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hmR).2
  nlinarith

lemma next_rawCutoff_ge {m : ℕ} (hm : 2 ≤ m) {D x : ℝ} (hD : 4 ≤ D) (hx : 0 ≤ x) :
    (m : ℝ) * (D * Real.exp x) / 4 ≤ rawCutoff m (D * Real.exp x) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have he : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hxnext : 4 ≤ D * Real.exp x := by
    have h := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ D)
    nlinarith
  have hfloor := Nat.lt_floor_add_one ((m : ℝ) * (D * Real.exp x) / 2)
  change _ < (rawCutoff m (D * Real.exp x) : ℝ) + 1 at hfloor
  nlinarith

lemma next_rawCutoff_pos {m : ℕ} (hm : 2 ≤ m) {D x : ℝ} (hD : 4 ≤ D) (hx : 0 ≤ x) :
    0 < rawCutoff m (D * Real.exp x) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < (m : ℝ) * (D * Real.exp x) / 4 := by positivity
  exact_mod_cast hpos.trans_le (next_rawCutoff_ge hm hD hx)

lemma survivorCutoff_le {m q : ℕ} (hm : 2 ≤ m) {D x : ℝ} (hD : 4 ≤ D) (hx : 0 ≤ x) :
    (survivorCutoff m q (rawCutoff m (D * Real.exp x)) : ℝ) ≤
      16 * (m * q : ℕ) / (D * Real.exp x) + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have heR : (0 : ℝ) < rawCutoff m (D * Real.exp x) := by
    exact_mod_cast next_rawCutoff_pos hm hD hx
  have hDpos : 0 < D * Real.exp x := by positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (4 : ℝ) * (m * q : ℕ) * m /
    rawCutoff m (D * Real.exp x) by positivity)
  change (survivorCutoff m q (rawCutoff m (D * Real.exp x)) : ℝ) < _ at hc
  have hb := next_rawCutoff_ge hm hD hx
  have hratio : (4 : ℝ) * (m * q : ℕ) * m / rawCutoff m (D * Real.exp x) ≤
      16 * (m * q : ℕ) / (D * Real.exp x) := by
    apply (div_le_div_iff₀ heR hDpos).2
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (16 : ℝ) * (m * q : ℕ) by positivity)
    nlinarith
  linarith

end ProbabilisticSerial.LowerBoundCutoffs
