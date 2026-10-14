import LowerBoundMarket

/-! Fixed parameters for an arbitrarily small loss in the lower-bound coefficient. -/

noncomputable section
open Filter
open scoped Topology

namespace ProbabilisticSerial.FixedQuotaParameters
open LowerBoundEntropy LowerBoundErrors LowerBoundBandErrors

structure Parameters (q : ℕ) (η : ℝ) where
  L : ℕ
  L_pos : 0 < L
  B : ℝ
  B_nonneg : 0 ≤ B
  c : ℝ
  c_pos : 0 < c
  D : ℝ
  D_ge_four : 4 ≤ D
  band_loss : 32 * (q : ℝ) ^ 2 / D ≤ η * q / 2
  θ : ℝ
  θ_pos : 0 < θ
  a : ℝ
  mean_lower : a ≤ 1 - 1 / (L + 1 : ℝ)
  coarse_budget : c + Real.log 2 ≤ 3 - Real.log 4
  fine_budget : c + (B + 1) * Real.exp (-B) ≤ η - Real.log (1 + η)
  rank_budget : c + (B + 1) * Real.exp (-B) ≤
    θ * (a - (1 - η)) - θ ^ 2 * (16 * (1 + Real.exp 1))

theorem parameters_exist (q : ℕ) {η : ℝ} (hη : 0 < η) : Nonempty (Parameters q η) := by
  let L : ℕ := ⌈2 / η⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (by positivity)
  have hLreal : 2 / η ≤ (L : ℝ) := Nat.le_ceil _
  let C : ℝ := 16 * (1 + Real.exp 1)
  have hC : 0 < C := by dsimp [C]; positivity
  let θ : ℝ := η / (4 * C)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let a : ℝ := 1 - η / 2
  let rankRate : ℝ := θ * (a - (1 - η)) - θ ^ 2 * C
  have hrank_eq : rankRate = η ^ 2 / (16 * C) := by
    unfold rankRate θ a
    field_simp
    <;> ring
  have hrank : 0 < rankRate := by rw [hrank_eq]; positivity
  let countRate : ℝ := η - Real.log (1 + η)
  have hcount : 0 < countRate := by
    have h := count_rate_pos (by linarith : (1 : ℝ) < 1 + η)
    dsimp [countRate]
    linarith
  obtain ⟨B, hB, hρ⟩ := exists_small_family_rate
    (show 0 < min countRate rankRate / 2 by exact div_pos (lt_min hcount hrank) (by norm_num))
  let ρ := (B + 1) * Real.exp (-B)
  have hρcount : ρ < countRate := by
    have hmin := min_le_left countRate rankRate
    change ρ < _ at hρ
    linarith
  have hρrank : ρ < rankRate := by
    have hmin := min_le_right countRate rankRate
    change ρ < _ at hρ
    linarith
  let β := min coarseRate (min (countRate - ρ) (rankRate - ρ))
  have hβ : 0 < β :=
    lt_min coarseRate_pos (lt_min (sub_pos.mpr hρcount) (sub_pos.mpr hρrank))
  let c := β / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcβ : c ≤ β := by dsimp [c]; linarith
  have hccoarse : c ≤ coarseRate := hcβ.trans (min_le_left _ _)
  have hcfine : c + ρ ≤ countRate := by
    have h := hcβ.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hcrank : c + ρ ≤ rankRate := by
    have h := hcβ.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let D : ℝ := 64 * q / η + 4
  have hD : 4 ≤ D := by
    dsimp [D]
    have h := div_nonneg (show 0 ≤ 64 * (q : ℝ) by positivity) hη.le
    linarith
  have hloss : 32 * (q : ℝ) ^ 2 / D ≤ η * q / 2 := by
    apply (div_le_iff₀ (show 0 < D by linarith)).2
    have heq : (η * (q : ℝ) / 2) * D = 32 * q ^ 2 + 2 * η * q := by
      dsimp [D]
      field_simp
      <;> ring
    rw [heq]
    have h := mul_nonneg hη.le (Nat.cast_nonneg q)
    linarith
  have hmean : a ≤ 1 - 1 / (L + 1 : ℝ) := by
    have hmul := (div_le_iff₀ hη).1 hLreal
    have hinv : 1 / (L + 1 : ℝ) ≤ η / 2 :=
      (div_le_iff₀ (by positivity)).2 (by nlinarith)
    dsimp [a]
    linarith
  refine ⟨⟨L, hL, B, hB, c, hc, D, hD, hloss, θ, hθ, a, hmean, ?_, hcfine, hcrank⟩⟩
  dsimp [coarseRate] at hccoarse
  linarith

end ProbabilisticSerial.FixedQuotaParameters
