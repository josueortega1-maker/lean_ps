import LowerBoundSchedule

/-! Eventual market-size conditions for fixed lower-bound parameters. -/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.LowerBoundMarket
open LowerBoundSchedule LowerBoundErrors FiniteLowerBound

def highCutoff (δ : ℝ) (m : ℕ) : ℕ := ⌊δ * m⌋₊

theorem highCutoff_le (δ : ℝ) (hδ : 0 ≤ δ) (m : ℕ) :
    (highCutoff δ m : ℝ) ≤ δ * m := Nat.floor_le (mul_nonneg hδ (Nat.cast_nonneg _))

theorem eventually_market_conditions (L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 2 ≤ m ∧ L ≤ m ∧ L ≤ highCutoff δ m ∧
      δ * m / 2 ≤ (highCutoff δ m : ℝ) ∧
      1 < Real.log m / 10 ∧ (L : ℝ) * Real.log m ≤ m ∧
      (2 : ℝ) * L ≤ (m : ℝ) ^ 2 := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun m : ℕ => (L : ℝ) * (Real.log m / m)) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, id_eq, mul_zero] using
      (tendsto_const_nhds (x := (L : ℝ))).mul h
  filter_upwards [eventually_ge_atTop (2 * L + 2),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * ((L : ℝ) + 1) / δ),
    hlog.eventually_gt_atTop 10, hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with m hm hlarge hlogm hratioM
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmLR : 2 * (L : ℝ) + 2 ≤ m := by exact_mod_cast hm
  have hδm : 2 * ((L : ℝ) + 1) ≤ δ * m := by
    have h := (div_le_iff₀ hδ).1 hlarge
    nlinarith
  have hf := Nat.lt_floor_add_one (δ * (m : ℝ))
  change δ * (m : ℝ) < (highCutoff δ m : ℝ) + 1 at hf
  have hhi : L ≤ highCutoff δ m := by
    have h : (L : ℝ) ≤ highCutoff δ m := by
      nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
    exact_mod_cast h
  have hscale : δ * m / 2 ≤ (highCutoff δ m : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  have hlogBound : (L : ℝ) * Real.log m ≤ m := by
    have h := mul_le_mul_of_nonneg_right hratioM.le hmR.le
    have heq : ((L : ℝ) * (Real.log m / m)) * m = L * Real.log m := by
      field_simp
    rw [heq, one_mul] at h
    exact h
  exact ⟨by omega, by omega, hhi, hscale, by linarith, hlogBound, by nlinarith⟩

theorem overhead_bound {m q : ℕ} {δ : ℝ} (hm : 0 < m) (hδ : 0 < δ)
    (hscale : δ * m / 2 ≤ (highCutoff δ m : ℝ)) :
    (4 : ℝ) * (m * q : ℕ) / highCutoff δ m ≤ 8 * q / δ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhi : (0 : ℝ) < highCutoff δ m := (by positivity : 0 < δ * m / 2).trans_le hscale
  apply (div_le_div_iff₀ hhi hδ).2
  rw [Nat.cast_mul]
  have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 8 * (q : ℝ) by positivity)
  nlinarith

theorem weighted_exceptionalBound_le {m q L lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    {α θ a K B c : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hhi : (hi : ℝ) ≤ m * Real.exp (-B))
    (hcoarse : c + Real.log 2 ≤ 3 - Real.log 4)
    (hfine : c + (B + 1) * Real.exp (-B) ≤ α - 1 - Real.log α)
    (hrank : c + (B + 1) * Real.exp (-B) ≤
      θ * (a - K) - θ ^ 2 * (16 * (1 + Real.exp 1))) :
    (K * (horizon m L / (m : ℝ))) *
      exceptionalBound m q (horizon m L) lo hi α θ a K ≤
        K * ((2 * (m : ℝ) ^ 3 + 3 * m) * Real.exp (-c * m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (horizon m L : ℝ) ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast (show horizon m L ≤ m ^ 2 by simpa [pow_two] using horizon_le_square m L)
  have hNm : horizon m L / (m : ℝ) ≤ m := (div_le_iff₀ hmR).2 (by nlinarith)
  have hb := exceptionalBound_le (N := horizon m L) (lo := lo) hq hB hc hhi hcoarse hfine hrank
  have hcoeff : (2 : ℝ) * ((horizon m L + 1 : ℕ) : ℝ) + 1 ≤ 2 * (m : ℝ) ^ 2 + 3 := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hpoly := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-c * m)).le
  have hbig := hb.trans hpoly
  have hmult := mul_le_mul_of_nonneg_left hbig
    (show 0 ≤ K * (horizon m L / (m : ℝ)) by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hNm hK
  have hprod := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ (2 * (m : ℝ) ^ 2 + 3) * Real.exp (-c * m) by positivity)
  apply hmult.trans
  convert hprod using 1 <;> ring

end ProbabilisticSerial.LowerBoundMarket
