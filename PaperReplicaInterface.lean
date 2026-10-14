import ReplicaPS
import FiniteFiveCertificate
import ReplicaExpectedRank

/-!
# Explicit integration points for the updated finite claims

The reusable finite implications retain explicit rank and arrival inputs.
The final three declarations discharge those inputs using the concrete
replica trace, for every positive integer number of types and quota.
-/

noncomputable section

namespace ProbabilisticSerial.PaperReplicaInterface

open ReplicaPS FiniteAtomicExposure FiniteExposure StandardLogStar FinitePhaseGrowth

theorem small_market_expected_rank {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (hm5 : m ≤ 5) :
    ReplicaPS.expectedPS m q < (logStar m : ℝ) + 17 / 5 := by
  have h := (expectedPS_bounds m q hm hq).2
  by_cases hm2 : m ≤ 2
  · have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    have hk : (0 : ℝ) ≤ logStar m := Nat.cast_nonneg _
    linarith
  · have hk : (2 : ℝ) ≤ logStar m := by exact_mod_cast logStar_ge_two (by omega : 3 ≤ m)
    have hmR : (m : ℝ) ≤ 5 := by exact_mod_cast hm5
    linarith

theorem expectedPS_lt_logStar_add_of_arrival_bounds
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {ι : Type*} [Fintype ι] (D : Data ι)
    (hrank : ReplicaPS.expectedPS m q ≤ value D 1)
    (hinterior : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ → cost D θ t ≤ phi θ (1 - t))
    (hendpoint : ∀ θ, 0 < θ → cost D θ 1 ≤ θ + Real.log (m : ℝ)) :
    ReplicaPS.expectedPS m q < (logStar m : ℝ) + 17 / 5 := by
  by_cases hsmall : m ≤ 5
  · exact small_market_expected_rank hm hq hsmall
  · exact hrank.trans_lt (logarithmic_bound D m (by omega) hinterior hendpoint)

theorem expectedPS_lt_five_of_arrival_bounds
    {m q : ℕ} (hm : 0 < m) (hmmax : m ≤ 10 ^ 80)
    {ι : Type*} [Fintype ι] (D : Data ι)
    (hrank : ReplicaPS.expectedPS m q ≤ value D 1)
    (hinterior : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ → cost D θ t ≤ phi θ (1 - t))
    (hendpoint : cost D 1600 1 ≤ 1600 + Real.log (m : ℝ)) :
    ReplicaPS.expectedPS m q < 5 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmaxR : (m : ℝ) ≤ (10 : ℝ) ^ 80 := by exact_mod_cast hmmax
  have hlog : Real.log (m : ℝ) ≤ 80 * Real.log 10 := by
    have h := Real.log_le_log hmR hmaxR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  exact hrank.trans_lt (FiniteFiveCertificate.value_lt_five D hinterior (by linarith))

/-- The finite expected PS type rank, for every positive integer quota. -/
theorem expectedPS_lt_logStar_add_three_point_four (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    ReplicaPS.expectedPS m q < (logStar m : ℝ) + 17 / 5 := by
  letI : Nonempty (Fin (m * q)) := ⟨⟨0, Nat.mul_pos hm hq⟩⟩
  exact expectedPS_lt_logStar_add_of_arrival_bounds hm hq
    (ReplicaChoiceMachine.actualExposure (m := m) (q := q))
    ReplicaChoiceMachine.expectedPS_le_actualExposure
    (fun t ht ht1 θ hθ => ReplicaChoiceMachine.actualExposure_cost_le t θ ht ht1 hθ)
    ReplicaChoiceMachine.actualExposure_cost_endpoint_le

theorem expectedPS_le_logStar_add_three_point_four (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    ReplicaPS.expectedPS m q ≤ (logStar m : ℝ) + 17 / 5 :=
  (expectedPS_lt_logStar_add_three_point_four m q hm hq).le

/-- The finite-range certificate applies to every positive integer quota. -/
theorem expectedPS_lt_five (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hmax : m ≤ 10 ^ 80) :
    ReplicaPS.expectedPS m q < 5 := by
  letI : Nonempty (Fin (m * q)) := ⟨⟨0, Nat.mul_pos hm hq⟩⟩
  exact expectedPS_lt_five_of_arrival_bounds hm hmax
    (ReplicaChoiceMachine.actualExposure (m := m) (q := q))
    ReplicaChoiceMachine.expectedPS_le_actualExposure
    (fun t ht ht1 θ hθ => ReplicaChoiceMachine.actualExposure_cost_le t θ ht ht1 hθ)
    (ReplicaChoiceMachine.actualExposure_cost_endpoint_le 1600 (by norm_num))

end ProbabilisticSerial.PaperReplicaInterface
