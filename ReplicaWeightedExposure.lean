import ReplicaCapacity

/-! Time-weighted fresh type arrivals equal actual type consumption. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS PSChoiceMachine AdaptiveCategorical
variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma weightedCompensator_history (profile : ReplicaPS.Profile m q)
    (X : List (Fin (m * q)) → Fin (m * q) → Bool)
    (z : List (Fin (m * q)) → ℝ) (θ : ℝ) (depth : ℕ) :
    weightedCompensator machineWeight X z θ (history profile depth) =
      ∑ k ∈ Finset.range depth,
        successProbability machineWeight X (history profile k) *
          (1 - Real.exp (-θ * z (history profile k))) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change weightedCompensator machineWeight X z θ
        (answer profile (history profile depth) :: history profile depth) = _
      rw [weightedCompensator, ih, Finset.sum_range_succ]

def profileExposureCost (profile : ReplicaPS.Profile m q) (θ t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m * q), ∑ i : Fin (m * q),
    arrivalWeight (history profile (r * (m * q) + i.val)) *
      (1 - Real.exp (-θ * max (t - roundTime profile r) 0))

def profileExposure (profile : ReplicaPS.Profile m q) : ℝ :=
  ∑ r ∈ Finset.range (m * q), ∑ i : Fin (m * q),
    arrivalWeight (history profile (r * (m * q) + i.val)) *
      max (1 - roundTime profile r) 0

lemma weightedCompensator_eq_exposure (profile : ReplicaPS.Profile m q) (θ t : ℝ) (g : Fin m)
    (hsurvive : ∀ r < m * q, roundTime profile r < t → g ∈ roundTypes profile r) :
    weightedCompensator machineWeight (entry g) (timeWeight t) θ
      (history profile ((m * q) * (m * q))) = profileExposureCost profile θ t := by
  rw [weightedCompensator_history, sum_slots]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  have hz : timeWeight t (history profile (r * (m * q) + i.val)) =
      max (t - roundTime profile r) 0 := by simp only [timeWeight, queryTime_at_slot]
  rw [hz]
  by_cases ht : roundTime profile r < t
  · rw [entry_successProbability profile _ g (by
      rw [queryTypes_at_slot]
      exact hsurvive r (Finset.mem_range.mp hr) ht)]
  · simp [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]

lemma entry_initial_weighted (profile : ReplicaPS.Profile m q) (t : ℝ)
    (i : Fin (m * q)) (g : Fin m) :
    timeWeight t (history profile i.val) *
      (if entry g (history profile i.val) (answer profile (history profile i.val)) then 1 else 0) =
      max (t - roundTime profile 0) 0 * choiceIndicator profile i g 0 := by
  have hA : (roundTypes profile 0).Nonempty := by
    rw [roundTypes_initial]
    exact ⟨g, Finset.mem_univ _⟩
  have htime := queryTime_at_slot profile 0 i
  have hactive := queryTypes_at_slot profile 0 i
  have hans := answer_type_at_slot profile 0 i hA
  simp only [Nat.zero_mul, Nat.zero_add] at htime hactive hans
  have hg : g ∈ queryTypes (history profile i.val) := by rw [hactive, roundTypes_initial]; simp
  have hs : stochasticRecording (history profile i.val) = true := by
    simp only [stochasticRecording, FreshQuery, previousType_at_slot_zero,
      hactive, hA, and_true, decide_true]
  simp only [timeWeight, htime, entry, hs, Bool.true_and, hg, true_and,
    decide_eq_true_eq, hans, choiceIndicator, roundChoice_eq profile 0 i hA]

lemma entry_successor_weighted (profile : ReplicaPS.Profile m q) (t : ℝ) (r : ℕ)
    (i : Fin (m * q)) (g : Fin m)
    (hsurvive : roundTime profile (r + 1) < t → g ∈ roundTypes profile (r + 1)) :
    timeWeight t (history profile ((r + 1) * (m * q) + i.val)) *
      (if entry g (history profile ((r + 1) * (m * q) + i.val))
        (answer profile (history profile ((r + 1) * (m * q) + i.val))) then 1 else 0) =
      max (t - roundTime profile (r + 1)) 0 *
        (choiceIndicator profile i g (r + 1) - choiceIndicator profile i g r) := by
  simp only [timeWeight, queryTime_at_slot]
  by_cases ht : roundTime profile (r + 1) < t
  · have hg := hsurvive ht
    let hA : (roundTypes profile (r + 1)).Nonempty := ⟨g, hg⟩
    let hprev : (roundTypes profile r).Nonempty := hA.mono (roundTypes_subset profile (Nat.le_succ r))
    simp only [entry, stochasticRecording, FreshQuery, previousType_at_slot_succ profile r i hA,
      queryTypes_at_slot, hA, true_and, hg, answer_type_at_slot profile (r + 1) i hA,
      Bool.and_eq_true, decide_eq_true_eq, choiceIndicator,
      roundChoice_eq profile (r + 1) i hA, roundChoice_eq profile r i hprev]
    by_cases hold : favorite (profile i) (roundTypes profile r) hprev = g
    · have hnew : favorite (profile i) (roundTypes profile (r + 1)) hA = g :=
        (ReplicaTrace.favorite_persists _ _ _ (roundTypes_subset profile (Nat.le_succ r))
          (hold ▸ hg)).trans hold
      simp [hold, hnew, hg]
    · by_cases hnew : favorite (profile i) (roundTypes profile (r + 1)) hA = g
      · have hgone : favorite (profile i) (roundTypes profile r) hprev ∉ roundTypes profile (r + 1) := by
          intro hm
          exact hold ((ReplicaTrace.favorite_persists _ _ _
            (roundTypes_subset profile (Nat.le_succ r)) hm).symm.trans hnew)
        simp [hold, hnew, hgone]
      · simp [hold, hnew]
  · simp [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]

lemma weightedSuccesses_eq_consumption (profile : ReplicaPS.Profile m q) (t : ℝ) (ht : t ≤ 1)
    (g : Fin m) (hsurvive : ∀ r < m * q, roundTime profile r < t → g ∈ roundTypes profile r) :
    weightedSuccesses (entry g) (timeWeight t) (history profile ((m * q) * (m * q))) =
      partialConsumption profile t g := by
  have hsurviveAll (r : ℕ) (hr : roundTime profile r < t) : g ∈ roundTypes profile r := by
    by_cases hrn : r < m * q
    · exact hsurvive r hrn hr
    · have hmono := roundTime_mono profile (Nat.le_of_not_gt hrn)
      rw [roundTime_terminal] at hmono
      linarith
  rw [weightedSuccesses_profileHistory, sum_slots, Finset.sum_comm]
  have heach (i : Fin (m * q)) :
      (∑ r ∈ Finset.range (m * q), timeWeight t (history profile (r * (m * q) + i.val)) *
        (if entry g (history profile (r * (m * q) + i.val))
          (answer profile (history profile (r * (m * q) + i.val))) then 1 else 0)) =
        ∑ r ∈ Finset.range (m * q), partialDuration profile t r * choiceIndicator profile i g r := by
    have h := sum_shifted_entries
      (fun r => max (t - roundTime profile r) 0) (choiceIndicator profile i g)
      (fun r => timeWeight t (history profile (r * (m * q) + i.val)) *
        (if entry g (history profile (r * (m * q) + i.val))
          (answer profile (history profile (r * (m * q) + i.val))) then 1 else 0)) (m * q)
      (by simpa using entry_initial_weighted profile t i g)
      (fun r => entry_successor_weighted profile t r i g (hsurviveAll (r + 1)))
      (by
        change max (t - roundTime profile (m * q)) 0 = 0
        rw [roundTime_terminal, max_eq_right (sub_nonpos.mpr ht)])
    simpa only [← partialDuration_eq_ramp] using h
  simp_rw [heach]
  rw [Finset.sum_comm, partialConsumption_eq]
  simp only [Finset.mul_sum]

end ProbabilisticSerial.ReplicaChoiceMachine
