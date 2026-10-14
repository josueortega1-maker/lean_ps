import FixedQuotaParameters
import PaperReplicaInterface

/-! The fixed-positive-quota lower asymptotic for the original replica PS model. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset Filter
open scoped BigOperators Topology

namespace ProbabilisticSerial.FixedQuotaLowerBound
open ReplicaPS ReplicaRawProcess ReplicaBandLower FiniteLowerBound LowerBoundBands
  LowerBoundCutoffs LowerBoundBandErrors LowerBoundSchedule LowerBoundMarket
  LowerBoundErrors FixedQuotaParameters StandardLogStar

theorem eventually_lower_with_loss (q : ℕ) (hq : 0 < q)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      ((1 - η) ^ 2 / (1 + η)) * (logStar m : ℝ) - C ≤ ReplicaPS.expectedPS m q := by
  let P : Parameters q η := Classical.choice (parameters_exist q hη)
  let δ := Real.exp (-P.B)
  have hδ : 0 < δ := Real.exp_pos _
  have hD : 1 ≤ P.D := by linarith [P.D_ge_four]
  have hK : 0 ≤ 1 - η := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hα : 0 < 1 + η := by linarith
  have hαq : 0 < (1 + η) * (q : ℝ) := mul_pos hα hqR
  have hαq1 : 1 ≤ (1 + η) * (q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    nlinarith
  obtain ⟨Cstar, hCstar⟩ := logStar_le_completedBands_add P.D hD
  let C : ℝ := ((1 - η) ^ 2 * q * Cstar + (1 - η) * (8 * q / δ) + 1) /
    ((1 + η) * q)
  refine ⟨C, ?_⟩
  have hweighted : Tendsto
      (fun m : ℕ => (1 - η) * ((2 * (m : ℝ) ^ 3 + 3 * m) * Real.exp (-P.c * m)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 1 - η)).mul (polynomial_error_tendsto P.c_pos)
  filter_upwards [eventually_market_conditions P.L hδ,
    (bandError_tendsto q).eventually (gt_mem_nhds (show 0 < η * (q : ℝ) / 2 by positivity)),
    hweighted.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with m hmarket hbandError hweightedM
  obtain ⟨hm2, hLm, hLhi, hhighScale, hstart, hlog, hsize⟩ := hmarket
  have hm : 0 < m := by omega
  letI : Nonempty (Fin (m * q)) := ⟨⟨0, Nat.mul_pos hm hq⟩⟩
  let reference : ReplicaPS.Profile m q := fun _ => Equiv.refl (Fin m)
  let N := horizon m P.L
  let J := completedBands P.D hD m
  let hi := highCutoff δ m
  have hhi : 0 < hi := P.L_pos.trans_le hLhi
  have hJscale := completed_band_scale_bound hD hstart (show J ≤ completedBands P.D hD m from le_rfl)
  have hHorizon : cutoffs m P.D J ≤ N :=
    rawCutoff_le_horizon hm P.L_pos hJscale.1 hJscale.2.le hlog hsize
  have hcutoff : N / (m : ℝ) ≤ (1 + η) * (m * q : ℕ) / P.L :=
    horizon_rank_cutoff hm P.L_pos hαq1
  have hfinite := expectedPS_ge_explicit_bands hm2 hq reference N J
    (cutoffs m P.D) (survivors m q P.D) (cutoffs_mono m hD) hHorizon
    hhi hLm hLhi (by linarith : 1 < 1 + η) hK P.θ_pos P.mean_lower hcutoff
    (fun j _ => schedule_mean hm2 P.D_ge_four j)
  have hbandSum : (J : ℝ) * ((1 - η) * q) ≤
      ∑ j ∈ Finset.range J,
        bandLowerValue m q (cutoffs m P.D j) (cutoffs m P.D (j + 1)) (survivors m q P.D j) 4 := by
    calc
      _ = ∑ _j ∈ Finset.range J, ((1 - η) * (q : ℝ)) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjJ : j ≤ completedBands P.D hD m := (Finset.mem_range.mp hj).le
        have hx := completed_band_scale_bound hD hstart hjJ
        have h := bandLowerValue_ge hm2 hq P.D_ge_four hx.1 hx.2.le
        change (q : ℝ) - 32 * q ^ 2 / P.D - bandError m q ≤
          bandLowerValue m q (cutoffs m P.D j) (cutoffs m P.D (j + 1)) (survivors m q P.D j) 4 at h
        linarith [P.band_loss]
  have hbandScaled := mul_le_mul_of_nonneg_left hbandSum hK
  have hhigh : (hi : ℝ) ≤ m * Real.exp (-P.B) := by
    simpa only [δ, mul_comm] using highCutoff_le δ hδ.le m
  have hfine : P.c + (P.B + 1) * Real.exp (-P.B) ≤
      (1 + η) - 1 - Real.log (1 + η) := by
    linarith [P.fine_budget]
  have hexception := weighted_exceptionalBound_le (L := P.L) (lo := P.L) hm hq
    hK P.B_nonneg P.c_pos.le hhigh P.coarse_budget hfine P.rank_budget
  have hexc : ((1 - η) * (N / (m : ℝ))) *
      exceptionalBound m q N P.L hi (1 + η) P.θ P.a (1 - η) ≤ 1 :=
    hexception.trans hweightedM.le
  have ho := mul_le_mul_of_nonneg_left (overhead_bound (q := q) hm hδ hhighScale) hK
  have hbase : (1 - η) ^ 2 * q * J - (1 - η) * (8 * q / δ) - 1 ≤
      ((1 + η) * q) * ReplicaPS.expectedPS m q := by
    nlinarith
  have hcount : (logStar m : ℝ) ≤ (J : ℝ) + Cstar := by exact_mod_cast hCstar m hm
  have hcountScaled := mul_le_mul_of_nonneg_left hcount
    (show 0 ≤ (1 - η) ^ 2 * (q : ℝ) by positivity)
  have hfinal : (1 - η) ^ 2 * q * (logStar m : ℝ) -
      ((1 - η) ^ 2 * q * Cstar + (1 - η) * (8 * q / δ) + 1) ≤
      ((1 + η) * q) * ReplicaPS.expectedPS m q := by
    nlinarith
  apply (mul_le_mul_iff_of_pos_right hαq).mp
  have heq : (((1 - η) ^ 2 / (1 + η)) * (logStar m : ℝ) - C) * ((1 + η) * q) =
      (1 - η) ^ 2 * q * (logStar m : ℝ) -
        ((1 - η) ^ 2 * q * Cstar + (1 - η) * (8 * q / δ) + 1) := by
    dsimp [C]
    field_simp
    <;> ring
  rw [heq]
  simpa only [mul_comm] using hfinal

/-- For each fixed positive integer quota, the expected PS type rank is
asymptotic to the standard natural-log iterated logarithm of the type count. -/
theorem expectedPS_div_logStar_tendsto_one (q : ℕ) (hq : 0 < q) :
    Tendsto (fun m : ℕ => ReplicaPS.expectedPS m q / (logStar m : ℝ))
      atTop (𝓝 1) := by
  have hstar : Tendsto (fun m : ℕ => (logStar m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp logStar_tendsto_atTop
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let η : ℝ := min ((1 - b) / 8) (1 / 4)
    have hη : 0 < η := lt_min (by linarith) (by norm_num)
    have hηquarter : η ≤ 1 / 4 := min_le_right _ _
    have hηgap : η ≤ (1 - b) / 8 := min_le_left _ _
    have hη1 : η < 1 := by linarith
    let A : ℝ := (1 - η) ^ 2 / (1 + η)
    have hA : 1 - 4 * η ≤ A := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + η)).2
      nlinarith [sq_nonneg η]
    have hbA : b < A := by linarith
    obtain ⟨C, hC⟩ := eventually_lower_with_loss q hq hη hη1
    have hlimit : Tendsto (fun m : ℕ => A - C / (logStar m : ℝ)) atTop (𝓝 A) := by
      simpa using (tendsto_const_nhds (x := A)).sub (hstar.const_div_atTop C)
    filter_upwards [hC, hstar.eventually_gt_atTop 0,
      hlimit.eventually (lt_mem_nhds hbA)] with m hm hpositive hlower
    apply hlower.trans_le
    apply (le_div_iff₀ hpositive).2
    have heq : (A - C / (logStar m : ℝ)) * (logStar m : ℝ) =
        A * (logStar m : ℝ) - C := by
      rw [sub_mul, div_mul_cancel₀ _ hpositive.ne']
    rw [heq]
    exact hm
  · intro b hb
    have hlimit : Tendsto (fun m : ℕ => 1 + (17 / 5 : ℝ) / (logStar m : ℝ))
        atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hstar.const_div_atTop (17 / 5))
    filter_upwards [eventually_gt_atTop (0 : ℕ), hstar.eventually_gt_atTop 0,
      hlimit.eventually (gt_mem_nhds hb)] with m hm hpositive hupper
    apply lt_of_le_of_lt _ hupper
    apply (div_le_iff₀ hpositive).2
    have heq : (1 + (17 / 5 : ℝ) / (logStar m : ℝ)) * (logStar m : ℝ) =
        (logStar m : ℝ) + 17 / 5 := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hpositive.ne']
    rw [heq]
    exact PaperReplicaInterface.expectedPS_le_logStar_add_three_point_four m q hm hq

/-- The lower-bound form, with any fixed relative loss. The quota is fixed
before the market size tends to infinity. -/
theorem eventually_expectedPS_ge (q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (1 - ε) * (logStar m : ℝ) ≤ ReplicaPS.expectedPS m q := by
  have hstar : Tendsto (fun m : ℕ => (logStar m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp logStar_tendsto_atTop
  filter_upwards [hstar.eventually_gt_atTop 0,
    (expectedPS_div_logStar_tendsto_one q hq).eventually
      (lt_mem_nhds (show 1 - ε < (1 : ℝ) by linarith))] with m hpositive hlower
  exact ((lt_div_iff₀ hpositive).1 hlower).le

end ProbabilisticSerial.FixedQuotaLowerBound
