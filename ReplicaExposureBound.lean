import ReplicaWeightedExposure
import FiniteFiveCertificate

/-! Quota-uniform finite exposure envelopes on the actual replica preference sample. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators
namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS PSChoiceMachine AdaptiveCategorical FiniteAtomicExposure FiniteExposure
variable {m q : ℕ} [Nonempty (Fin (m * q))]

def arrivalSupermartingale (profile : ReplicaPS.Profile m q) (θ t : ℝ) (g : Fin m) : ℝ :=
  weightedArrivalProcess machineWeight (entry g) (timeWeight t) θ
    (history profile ((m * q) * (m * q)))

lemma arrivalSupermartingale_pos (profile : ReplicaPS.Profile m q) (θ t : ℝ) (g : Fin m) :
    0 < arrivalSupermartingale profile θ t g := Real.exp_pos _

lemma expected_arrivalSupermartingale_le_one (θ t : ℝ) (g : Fin m) :
    (𝔼 profile ∈ ReplicaPS.profileSample m q, arrivalSupermartingale profile θ t g) ≤ 1 :=
  profile_weightedArrivalProcess_expectation_le_one (entry g) (timeWeight t) θ ((m * q) * (m * q))

lemma arrivalSupermartingale_eq (profile : ReplicaPS.Profile m q) (θ t : ℝ) (ht : t ≤ 1) (g : Fin m)
    (hsurvive : ∀ r < m * q, roundTime profile r < t →
      g ∈ roundTypes profile r) :
    arrivalSupermartingale profile θ t g =
      Real.exp (profileExposureCost profile θ t - θ * ((q : ℝ) - residual profile t g)) := by
  unfold arrivalSupermartingale weightedArrivalProcess
  rw [weightedCompensator_eq_exposure profile θ t g hsurvive,
    weightedSuccesses_eq_consumption profile t ht g hsurvive]
  congr 1
  rw [residual_eq]
  ring

theorem expected_profileExposureCost_le (t θ : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hθ : 0 < θ) :
    (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposureCost profile θ t) ≤ phi ((q : ℝ) * θ) (1 - t) := by
  classical
  let S : ReplicaPS.Profile m q → Finset (Fin m) := fun profile =>
    Finset.univ.filter (fun g => 0 < residual profile t g)
  have hsum (profile : ReplicaPS.Profile m q) :
      ∑ g ∈ S profile, residual profile t g = (m : ℝ) * q * (1 - t) := by
    have heq : (∑ g ∈ S profile, residual profile t g) =
        ∑ g : Fin m, residual profile t g := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g hgun hg
      have hnot : ¬ 0 < residual profile t g := by simpa [S] using hg
      exact le_antisymm (le_of_not_gt hnot) (residual_nonneg _ _ _)
    rw [heq, sum_residual profile t ht.le ht1.le]
  have h := FiniteSurvivor.expected_compensator_le (type_count_pos (m := m) (q := q))
    (ReplicaPS.profileSample m q) (ReplicaPS.profileSample_nonempty m q)
    (q := (q : ℝ)) (θ := θ) (u := 1 - t) (by exact_mod_cast (quota_pos (m := m) (q := q))) hθ (by linarith)
    S (fun p g => residual p t g) (fun p g => arrivalSupermartingale p θ t g)
    (fun p => profileExposureCost p θ t)
    (fun p _ g _ => residual_le_quota p t g)
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
    (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposureCost profile θ 1) ≤
      (q : ℝ) * θ + Real.log (m : ℝ) := by
  have h := FiniteSurvivor.expected_endpoint_compensator_le (type_count_pos (m := m) (q := q))
    (ReplicaPS.profileSample m q) (ReplicaPS.profileSample_nonempty m q) q θ
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

def rawExposure : Data (ReplicaPS.Profile m q × (Fin (m * q) × Fin (m * q))) where
  weight j := arrivalWeight (history j.1 (j.2.1.val * (m * q) + j.2.2.val)) /
    (ReplicaPS.profileSample m q).card
  time j := roundTime j.1 j.2.1.val
  weight_nonneg j := div_nonneg (arrivalWeight_nonneg _) (Nat.cast_nonneg _)
  time_nonneg j := roundTime_nonneg _ _

lemma rawExposure_value : value (rawExposure (m := m) (q := q)) 1 =
    𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposure profile := by
  rw [Finset.expect_eq_sum_div_card]
  unfold value rawExposure
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_div, ReplicaRevelation.profileSample_eq_univ]
  apply Finset.sum_congr rfl
  intro p hp
  unfold profileExposure
  rw [← sum_fin_rounds]
  simp only [Finset.sum_div, div_mul_eq_mul_div]

lemma rawExposure_cost (θ t : ℝ) : cost (rawExposure (m := m) (q := q)) θ t =
    𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposureCost profile θ t := by
  rw [Finset.expect_eq_sum_div_card]
  unfold cost rawExposure
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_div, ReplicaRevelation.profileSample_eq_univ]
  apply Finset.sum_congr rfl
  intro p hp
  unfold profileExposureCost
  rw [← sum_fin_rounds]
  simp only [arrivalCost, Finset.sum_div, div_mul_eq_mul_div]

def actualExposure : Data (ReplicaPS.Profile m q × (Fin (m * q) × Fin (m * q))) where
  weight j := (rawExposure (m := m) (q := q)).weight j / q
  time j := (rawExposure (m := m) (q := q)).time j
  weight_nonneg j := div_nonneg ((rawExposure (m := m) (q := q)).weight_nonneg j) (Nat.cast_nonneg _)
  time_nonneg j := (rawExposure (m := m) (q := q)).time_nonneg j

lemma actualExposure_value : value (actualExposure (m := m) (q := q)) 1 =
    (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposure profile) / q := by
  rw [← rawExposure_value]
  simp only [value, actualExposure, Finset.sum_div, div_mul_eq_mul_div]

lemma actualExposure_cost (θ t : ℝ) : cost (actualExposure (m := m) (q := q)) θ t =
    (𝔼 profile ∈ ReplicaPS.profileSample m q, profileExposureCost profile θ t) / q := by
  rw [← rawExposure_cost]
  simp only [cost, actualExposure, Finset.sum_div, div_mul_eq_mul_div]

theorem actualExposure_cost_le (t θ : ℝ) (ht : 0 < t) (ht1 : t < 1) (hθ : 0 < θ) :
    cost (actualExposure (m := m) (q := q)) θ t ≤ phi θ (1 - t) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (quota_pos (m := m) (q := q))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt (quota_pos (m := m) (q := q))
  rw [actualExposure_cost]
  calc
    _ ≤ phi ((q : ℝ) * θ) (1 - t) / q :=
      div_le_div_of_nonneg_right (expected_profileExposureCost_le t θ ht ht1 hθ) hqR.le
    _ = (phi ((q : ℝ) * θ) (1 - t) / ((q : ℝ) * θ)) * θ := by
      field_simp [hqR.ne', hθ.ne']
      ring
    _ ≤ (phi θ (1 - t) / θ) * θ := mul_le_mul_of_nonneg_right
      (phi_quota_reduction hq1 hθ (by linarith) (by linarith)) hθ.le
    _ = _ := div_mul_cancel₀ _ hθ.ne'

/-- Retain the quota scaling needed for growing-quota expectation bounds. -/
theorem actualExposure_cost_endpoint_quota_le (θ : ℝ) (hθ : 0 < θ) :
    cost (actualExposure (m := m) (q := q)) θ 1 ≤
      θ + Real.log (m : ℝ) / (q : ℝ) := by
  have hq : (0 : ℝ) < q := by
    exact_mod_cast (ReplicaChoiceMachine.quota_pos (m := m) (q := q))
  rw [actualExposure_cost]
  calc
    _ ≤ ((q : ℝ) * θ + Real.log (m : ℝ)) / (q : ℝ) :=
      div_le_div_of_nonneg_right
        (expected_profileExposureCost_endpoint_le (m := m) (q := q) θ hθ) hq.le
    _ = θ + Real.log (m : ℝ) / (q : ℝ) := by
      field_simp [hq.ne']
      <;> ring

/-- The quota-uniform envelope used by the logarithmic phase bound. -/
theorem actualExposure_cost_endpoint_le (θ : ℝ) (hθ : 0 < θ) :
    cost (actualExposure (m := m) (q := q)) θ 1 ≤ θ + Real.log (m : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt (quota_pos (m := m) (q := q))
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt (type_count_pos (m := m) (q := q))
  exact (actualExposure_cost_endpoint_quota_le θ hθ).trans
    (add_le_add_left (div_le_self (Real.log_nonneg hm1) hq1) θ)

end ProbabilisticSerial.ReplicaChoiceMachine
