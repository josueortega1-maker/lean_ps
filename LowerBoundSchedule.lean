import LowerBoundBandErrors

/-! The deterministic band schedule and its polynomial raw horizon. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundSchedule
open LowerBoundBands LowerBoundCutoffs StandardLogStar

theorem bandScale_mono {a D : ℝ} (hD : 1 ≤ D) : Monotone (bandScale a D) := by
  apply monotone_nat_of_le_succ
  intro j
  have h1 := Real.add_one_le_exp (bandScale a D j)
  have h2 := le_mul_of_one_le_left (Real.exp_pos (bandScale a D j)).le hD
  change bandScale a D j ≤ D * Real.exp (bandScale a D j)
  linarith

theorem bandScale_lt_before_index (a D target : ℝ) (hD : 1 ≤ D)
    {j : ℕ} (hj : j < bandIndex a D target hD) : bandScale a D j < target :=
  lt_of_not_ge (Nat.find_min (exists_bandScale_ge (a := a) hD target) hj)

def completedBands (D : ℝ) (hD : 1 ≤ D) (m : ℕ) : ℕ :=
  bandIndex 1 D (Real.log m / 10) hD - 1

theorem completedBands_le_logStar (D : ℝ) (hD : 1 ≤ D) (m : ℕ) :
    completedBands D hD m ≤ logStar m :=
  (Nat.sub_le _ _).trans (bandIndex_le_logStar (by norm_num) hD m)

theorem logStar_le_completedBands_add (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℕ, ∀ m : ℕ, 0 < m → logStar m ≤ completedBands D hD m + C := by
  obtain ⟨C, hC⟩ := logStar_le_bandIndex_add_constant (a := 1) (by norm_num) hD
  refine ⟨C + 1, ?_⟩
  intro m hm
  have h := hC m hm
  unfold completedBands
  omega

lemma bandIndex_pos {D : ℝ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 < Real.log m / 10) :
    0 < bandIndex 1 D (Real.log m / 10) hD := by
  have h := bandIndex_spec 1 D (Real.log m / 10) hD
  by_contra hn
  have hz : bandIndex 1 D (Real.log m / 10) hD = 0 := by omega
  rw [hz] at h
  change Real.log m / 10 ≤ 1 at h
  linarith

theorem completed_band_scale_bound {D : ℝ} (hD : 1 ≤ D) {m j : ℕ}
    (hstart : 1 < Real.log m / 10) (hj : j ≤ completedBands D hD m) :
    0 ≤ bandScale 1 D j ∧ bandScale 1 D j < Real.log m / 10 := by
  refine ⟨bandScale_nonneg (by norm_num) hD j, ?_⟩
  apply bandScale_lt_before_index 1 D _ hD
  have hp := bandIndex_pos hD hstart
  unfold completedBands at hj
  omega

def cutoffs (m : ℕ) (D : ℝ) (j : ℕ) : ℕ := rawCutoff m (bandScale 1 D j)

theorem cutoffs_mono (m : ℕ) {D : ℝ} (hD : 1 ≤ D) : Monotone (cutoffs m D) :=
  (rawCutoff_mono m).comp (bandScale_mono hD)

def survivors (m q : ℕ) (D : ℝ) (j : ℕ) : ℕ :=
  survivorCutoff m q (cutoffs m D (j + 1))

theorem schedule_mean {m q : ℕ} (hm : 2 ≤ m) {D : ℝ} (hD : 4 ≤ D) (j : ℕ) :
    (4 : ℝ) * (m * q : ℕ) ≤ cutoffs m D (j + 1) * ((survivors m q D j : ℝ) / m) := by
  apply survivorCutoff_mean (by omega : 0 < m)
  exact next_rawCutoff_pos hm hD (bandScale_nonneg (by norm_num) (by linarith) j)

def horizon (m L : ℕ) : ℕ := m * m / L

theorem horizon_le_square (m L : ℕ) : horizon m L ≤ m * m := Nat.div_le_self _ _

theorem horizon_rank_cutoff {m q L : ℕ} (hm : 0 < m) (hL : 0 < L)
    {α : ℝ} (hαq : 1 ≤ α * q) :
    horizon m L / (m : ℝ) ≤ α * (m * q : ℕ) / L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hN : (horizon m L : ℝ) * L ≤ (m : ℝ) * m := by
    exact_mod_cast Nat.div_mul_le_self (m * m) L
  apply (div_le_div_iff₀ hmR hLR).2
  rw [Nat.cast_mul]
  have h := mul_le_mul_of_nonneg_right hαq (show 0 ≤ (m : ℝ) * m by positivity)
  nlinarith

theorem rawCutoff_le_horizon {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    {x : ℝ} (hx : 0 ≤ x) (hupper : x ≤ Real.log m / 10)
    (hlog : (L : ℝ) * Real.log m ≤ m) (hsize : (2 : ℝ) * L ≤ (m : ℝ) ^ 2) :
    rawCutoff m x ≤ horizon m L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hN : (m : ℝ) * m < L * ((horizon m L : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ (m * m) hL
  have hk := rawCutoff_le m hx
  have hku := mul_le_mul_of_nonneg_left hupper hmR.le
  have hKL := mul_le_mul_of_nonneg_right hk hLR.le
  have huL := mul_le_mul_of_nonneg_right hku hLR.le
  have hlogm := mul_le_mul_of_nonneg_left hlog hmR.le
  have hbound : (rawCutoff m x : ℝ) ≤ horizon m L := by
    apply (mul_le_mul_iff_of_pos_right hLR).mp
    nlinarith
  exact_mod_cast hbound

end ProbabilisticSerial.LowerBoundSchedule
