import StandardLogStar
import Mathlib.Tactic

/-!
# Exponential bands for the fixed-quota lower bound

For fixed starting value and multiplier, the number of bands needed to
reach `log m / 10` differs from the manuscript's literal `logStar m` by a
bounded additive constant. This is an analytic counting result; it does
not claim that a PS run pays a positive expected cost in each band.
-/

noncomputable section
open Filter

namespace ProbabilisticSerial.LowerBoundBands
open PhaseIntegral StandardLogStar

def bandScale (a D : ℝ) : ℕ → ℝ
  | 0 => a
  | j + 1 => D * Real.exp (bandScale a D j)

lemma iteratedExp_le_bandScale {a D : ℝ} (hD : 1 ≤ D) (j : ℕ) :
    iteratedExp a j ≤ bandScale a D j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change Real.exp (iteratedExp a j) ≤ D * Real.exp (bandScale a D j)
      calc
        _ ≤ Real.exp (bandScale a D j) := Real.exp_le_exp.mpr ih
        _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hD

lemma bandScale_nonneg {a D : ℝ} (ha : 0 ≤ a) (hD : 1 ≤ D) (j : ℕ) :
    0 ≤ bandScale a D j := by
  cases j with
  | zero => exact ha
  | succ j => exact mul_nonneg (by linarith) (Real.exp_pos _).le

lemma bandScale_add_shift_le {a D : ℝ} (ha : 0 ≤ a) (hD : 1 ≤ D) (j : ℕ) :
    bandScale a D j + (1 + Real.log D) ≤ iteratedExp (a + (1 + Real.log D)) j := by
  have hDpos : 0 < D := by linarith
  have hshift : 1 + Real.log D ≤ D := by linarith [Real.log_le_sub_one_of_pos hDpos]
  have hexpshift : 2 * D ≤ Real.exp (1 + Real.log D) := by
    rw [Real.exp_add, Real.exp_log hDpos]
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact mul_le_mul_of_nonneg_right he hDpos.le
  induction j with
  | zero => rfl
  | succ j ih =>
      have hx := bandScale_nonneg ha hD j
      have he : 1 ≤ Real.exp (bandScale a D j) := Real.one_le_exp hx
      have hmul := mul_le_mul_of_nonneg_left he hDpos.le
      have hlarge := mul_le_mul_of_nonneg_left hexpshift (Real.exp_pos (bandScale a D j)).le
      calc
        bandScale a D (j + 1) + (1 + Real.log D) ≤
            Real.exp (bandScale a D j) * Real.exp (1 + Real.log D) := by
          dsimp [bandScale]
          nlinarith
        _ = Real.exp (bandScale a D j + (1 + Real.log D)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (iteratedExp (a + (1 + Real.log D)) j) := Real.exp_le_exp.mpr ih
        _ = _ := rfl

lemma bandScale_le_iteratedExp {a D : ℝ} (ha : 0 ≤ a) (hD : 1 ≤ D) (j : ℕ) :
    bandScale a D j ≤ iteratedExp (a + (1 + Real.log D)) j := by
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  linarith [bandScale_add_shift_le ha hD j]

lemma iteratedExp_add (a : ℝ) (k j : ℕ) :
    iteratedExp (iteratedExp a k) j = iteratedExp a (k + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      change Real.exp (iteratedExp (iteratedExp a k) j) = iteratedExp a (k + (j + 1))
      rw [ih, ← Nat.add_assoc, iteratedExp_succ]

lemma iteratedExp_index_mono (a : ℝ) : Monotone (iteratedExp a) := by
  apply monotone_nat_of_le_succ
  intro j
  have := Real.add_one_le_exp (iteratedExp a j)
  simpa only [iteratedExp_succ] using (show iteratedExp a j ≤ Real.exp (iteratedExp a j) by linarith)

lemma exists_bandScale_ge {a D : ℝ} (hD : 1 ≤ D) (target : ℝ) :
    ∃ j, target ≤ bandScale a D j := by
  obtain ⟨j, hj⟩ := exists_iteratedExp_ge a target
  exact ⟨j, hj.trans (iteratedExp_le_bandScale hD j)⟩

def bandIndex (a D target : ℝ) (hD : 1 ≤ D) : ℕ :=
  Nat.find (exists_bandScale_ge (a := a) hD target)

theorem bandIndex_spec (a D target : ℝ) (hD : 1 ≤ D) :
    target ≤ bandScale a D (bandIndex a D target hD) :=
  Nat.find_spec (exists_bandScale_ge (a := a) hD target)

lemma ten_mul_le_exp {x : ℝ} (hx : 40 ≤ x) : 10 * x ≤ Real.exp x := by
  have he := Real.add_one_le_exp (x / 2)
  have hsq := mul_self_le_mul_self (by linarith : 0 ≤ x / 2 + 1) he
  have hexp : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add, add_halves]
  rw [hexp] at hsq
  nlinarith [mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x - 40)]

theorem bandIndex_le_logStar {a D : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (m : ℕ) :
    bandIndex a D (Real.log m / 10) hD ≤ logStar m := by
  apply Nat.find_min'
  have hlog : Real.log (m : ℝ) / 10 ≤ m := by
    by_cases hm : m = 0
    · subst m; simp
    · have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      linarith [Real.log_le_sub_one_of_pos hmR]
  exact hlog.trans ((cast_le_iteratedExp_logStar m).trans
    ((iteratedExp_start_mono ha _).trans (iteratedExp_le_bandScale hD _)))

/-- The additive loss depends only on the fixed band parameters, not on m. -/
theorem logStar_le_bandIndex_add_constant {a D : ℝ} (ha : 0 ≤ a) (hD : 1 ≤ D) :
    ∃ C : ℕ, ∀ m : ℕ, 0 < m →
      logStar m ≤ bandIndex a D (Real.log m / 10) hD + C := by
  let A := a + (1 + Real.log D) + 40
  obtain ⟨k, hk⟩ := exists_iteratedExp_ge 1 A
  refine ⟨k + 2, ?_⟩
  intro m hm
  let j := bandIndex a D (Real.log m / 10) hD
  have hA : 40 ≤ A := by
    dsimp [A]
    linarith [Real.log_nonneg hD]
  have hstart : a + (1 + Real.log D) ≤ A := by dsimp [A]; linarith
  have hband : bandScale a D j ≤ iteratedExp A j :=
    (bandScale_le_iteratedExp ha hD j).trans (iteratedExp_start_mono hstart j)
  have hreach := bandIndex_spec a D (Real.log m / 10) hD
  have hlarge : 40 ≤ iteratedExp A j := by linarith [add_natCast_le_iteratedExp A j]
  have hlog : Real.log (m : ℝ) ≤ Real.exp (iteratedExp A j) := by
    have hten := ten_mul_le_exp hlarge
    change Real.log (m : ℝ) / 10 ≤ bandScale a D j at hreach
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htower : (m : ℝ) ≤ iteratedExp A (j + 2) := by
    simpa [iteratedExp_succ, Real.exp_log hmR] using Real.exp_le_exp.mpr hlog
  have hfinal : (m : ℝ) ≤ iteratedExp 1 (k + (j + 2)) := by
    apply htower.trans
    rw [← iteratedExp_add 1 k (j + 2)]
    exact iteratedExp_start_mono hk _
  obtain ⟨i, hi, hsmall⟩ := exists_iteratedLog_le_one_of_le_iteratedExp
    (k + (j + 2)) m (by exact_mod_cast hm) hfinal
  have hmin : logStar m ≤ i := Nat.find_min' _ hsmall
  dsimp [j] at hi
  omega

theorem logStar_tendsto_atTop : Tendsto logStar atTop atTop := by
  apply tendsto_atTop.2
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt (iteratedExp 1 k)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hlarge : iteratedExp 1 k < (m : ℝ) :=
    hN.trans_le (by exact_mod_cast hm)
  by_contra hn
  have hsmall := iteratedExp_index_mono 1 (by omega : logStar m ≤ k)
  linarith [cast_le_iteratedExp_logStar m]

end ProbabilisticSerial.LowerBoundBands
