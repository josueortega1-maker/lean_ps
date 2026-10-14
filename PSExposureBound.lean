import PSWeightedExposure
import FiniteFiveCertificate

/-! Unconditional finite exposure bounds on uniform one-copy PS profiles. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess AdaptiveCategorical FiniteAtomicExposure FiniteExposure
variable {n : ℕ} [Nonempty (Fin n)]

def arrivalSupermartingale (profile : Profile n) (θ t : ℝ) (g : Fin n) : ℝ :=
  weightedArrivalProcess machineWeight (setEntry {g}) (timeWeight t) θ
    (profileHistory profile (n * n))

lemma arrivalSupermartingale_pos (profile : Profile n) (θ t : ℝ) (g : Fin n) :
    0 < arrivalSupermartingale profile θ t g := Real.exp_pos _

lemma expected_arrivalSupermartingale_le_one (θ t : ℝ) (g : Fin n) :
    (𝔼 profile ∈ preferenceProfileSample n, arrivalSupermartingale profile θ t g) ≤ 1 :=
  profile_weightedArrivalProcess_expectation_le_one (setEntry {g}) (timeWeight t) θ (n * n)

lemma arrivalSupermartingale_eq (profile : Profile n) (θ t : ℝ) (ht : t ≤ 1) (g : Fin n)
    (hsurvive : ∀ r < n, roundTime profile r < t →
      g ∈ activeGoods (profileSupply profile r)) :
    arrivalSupermartingale profile θ t g =
      Real.exp (profileExposureCost profile θ t - θ * (1 - residual profile t g)) := by
  unfold arrivalSupermartingale weightedArrivalProcess
  rw [weightedCompensator_eq_exposure profile θ t g hsurvive,
    weightedSuccesses_eq_consumption profile t ht g hsurvive]
  congr 1
  unfold residual
  ring

theorem expected_profileExposureCost_le (t θ : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hθ : 0 < θ) :
    (𝔼 profile ∈ preferenceProfileSample n, profileExposureCost profile θ t) ≤ phi θ (1 - t) := by
  classical
  let S : Profile n → Finset (Fin n) := fun profile =>
    Finset.univ.filter (fun g => 0 < residual profile t g)
  have hsum (profile : Profile n) :
      ∑ g ∈ S profile, residual profile t g = n * (1 : ℝ) * (1 - t) := by
    have heq : (∑ g ∈ S profile, residual profile t g) =
        ∑ g : Fin n, residual profile t g := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g hgun hg
      have hnot : ¬ 0 < residual profile t g := by simpa [S] using hg
      exact le_antisymm (le_of_not_gt hnot) (residual_nonneg _ _ _)
    rw [heq, sum_residual profile t ht.le ht1.le, mul_one]
  have h := FiniteSurvivor.expected_compensator_le (market_pos (n := n))
    (preferenceProfileSample n) (preferenceProfileSample_nonempty n)
    (q := 1) (θ := θ) (u := 1 - t) (by norm_num) hθ (by linarith)
    S (fun p g => residual p t g) (fun p g => arrivalSupermartingale p θ t g)
    (fun p => profileExposureCost p θ t)
    (fun p _ g _ => residual_le_one p t g)
    (fun p _ => hsum p)
    (fun p _ g => arrivalSupermartingale_pos p θ t g)
    (by
      intro p hp g hg
      have hpos : 0 < residual p t g := (Finset.mem_filter.mp hg).2
      dsimp only
      rw [arrivalSupermartingale_eq p θ t ht1.le g (by
        intro r hr hrt
        exact residual_pos_implies_active p t g hpos r hr.le hrt.le)])
    (expected_arrivalSupermartingale_le_one θ t)
  simpa using h

theorem expected_profileExposureCost_endpoint_le (θ : ℝ) (hθ : 0 < θ) :
    (𝔼 profile ∈ preferenceProfileSample n, profileExposureCost profile θ 1) ≤
      θ + Real.log (n : ℝ) := by
  have h := FiniteSurvivor.expected_endpoint_compensator_le (market_pos (n := n))
    (preferenceProfileSample n) (preferenceProfileSample_nonempty n) 1 θ
    (fun p g => arrivalSupermartingale p θ 1 g) (fun p => profileExposureCost p θ 1)
    (fun p _ g => arrivalSupermartingale_pos p θ 1 g)
    (by
      intro p hp
      obtain ⟨g, hg⟩ := exists_last_survivor p
      refine ⟨g, ?_⟩
      dsimp only
      rw [arrivalSupermartingale_eq p θ 1 le_rfl g (fun r _ hr => hg r hr)]
      apply Real.exp_le_exp.mpr
      have hres := residual_nonneg p 1 g
      nlinarith)
    (expected_arrivalSupermartingale_le_one θ 1)
  simpa using h

lemma preferenceProfileSample_eq_univ : preferenceProfileSample n = Finset.univ := by
  ext p
  simp [preferenceProfileSample, UniformProduct.productSample, preferenceSample, permutationSample]

lemma sum_fin_rounds (f : ℕ → ℝ) : (∑ r : Fin n, f r.val) = ∑ r ∈ Finset.range n, f r := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [dif_pos (Finset.mem_range.mp hr)]

def actualExposure : Data (Profile n × (Fin n × Fin n)) where
  weight j := arrivalWeight (profileHistory j.1 (j.2.1.val * n + j.2.2.val)) /
    (preferenceProfileSample n).card
  time j := roundTime j.1 j.2.1.val
  weight_nonneg j := div_nonneg (arrivalWeight_nonneg _) (Nat.cast_nonneg _)
  time_nonneg j := roundTime_nonneg _ _

lemma actualExposure_value : value (actualExposure (n := n)) 1 =
    𝔼 profile ∈ preferenceProfileSample n, profileExposure profile := by
  rw [Finset.expect_eq_sum_div_card]
  unfold value actualExposure
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_div, preferenceProfileSample_eq_univ]
  apply Finset.sum_congr rfl
  intro p hp
  unfold profileExposure
  rw [← sum_fin_rounds]
  simp only [Finset.sum_div, div_mul_eq_mul_div]

lemma actualExposure_cost (θ t : ℝ) : cost (actualExposure (n := n)) θ t =
    𝔼 profile ∈ preferenceProfileSample n, profileExposureCost profile θ t := by
  rw [Finset.expect_eq_sum_div_card]
  unfold cost actualExposure
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_div, preferenceProfileSample_eq_univ]
  apply Finset.sum_congr rfl
  intro p hp
  unfold profileExposureCost
  rw [← sum_fin_rounds]
  simp only [arrivalCost, Finset.sum_div, div_mul_eq_mul_div]

theorem expected_profileExposure_lt_logStar_add (hn : 3 ≤ n) :
    (𝔼 profile ∈ preferenceProfileSample n, profileExposure profile) <
      (StandardLogStar.logStar n : ℝ) + 17 / 5 := by
  rw [← actualExposure_value]
  apply logarithmic_bound actualExposure n hn
  · intro t ht ht1 θ hθ
    rw [actualExposure_cost]
    exact expected_profileExposureCost_le t θ ht ht1 hθ
  · intro θ hθ
    rw [actualExposure_cost]
    exact expected_profileExposureCost_endpoint_le θ hθ

end ProbabilisticSerial.PSChoiceMachine
