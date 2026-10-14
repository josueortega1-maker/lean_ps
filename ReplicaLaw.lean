import ReplicaHistory
import PSExpectedRank
import WeightedArrival

/-! The exact finite-profile transition law and weighted arrival transfer. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS ReplicaRevelation PSChoiceMachine AdaptiveCategorical
variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma pathFiber_nonempty (reference : ReplicaPS.Profile m q) (depth : ℕ) :
    (pathFiber depth (history reference depth)).Nonempty := by
  refine ⟨reference, ?_⟩
  simp only [pathFiber, Finset.mem_filter, profileSample_eq_univ, Finset.mem_univ, true_and]

/-- The conditional law is defined by the exact finite preference fiber.
Unreachable histories use a deterministic total extension. -/
def machineWeight (h : List (Fin (m * q))) (c : Fin (m * q)) : ℝ :=
  if (pathFiber h.length h).Nonempty then
    𝔼 p ∈ pathFiber h.length h, if answer p h = c then 1 else 0
  else if defaultGood = c then 1 else 0

lemma machineWeight_expectation (h : List (Fin (m * q)))
    (hc : (pathFiber h.length h).Nonempty) (F : Fin (m * q) → ℝ) :
    (∑ c, machineWeight h c * F c) = 𝔼 p ∈ pathFiber h.length h, F (answer p h) := by
  simp only [machineWeight, if_pos hc]
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro p hp
  simp only [ite_mul, one_mul, zero_mul]
  simp

theorem machineWeight_valid : ValidLaw (machineWeight (m := m) (q := q)) := by
  intro h
  constructor
  · intro c
    unfold machineWeight
    split_ifs
    · exact Finset.expect_nonneg (fun _ _ => by positivity)
    · norm_num
    · norm_num
  · by_cases hc : (pathFiber h.length h).Nonempty
    · have hh := machineWeight_expectation h hc (fun _ => 1)
      simpa only [mul_one, Finset.expect_const hc] using hh
    · simp [machineWeight, hc]

theorem profile_supermartingale_expectation_le
    {Z : List (Fin (m * q)) → ℝ} (hZ : IsTreeSupermartingale machineWeight Z) :
    ∀ depth, (𝔼 profile ∈ ReplicaPS.profileSample m q, Z (history profile depth)) ≤ Z [] := by
  intro depth
  induction depth with
  | zero => simpa only [history, profileHistory_zero,
      Finset.expect_const (profileSample_nonempty m q)] using (le_refl (Z []))
  | succ depth ih =>
      apply le_trans _ ih
      apply expect_le_of_fiberwise (ReplicaPS.profileSample m q) (fun p => history p depth)
      intro reference href
      change (𝔼 other ∈ pathFiber depth (history reference depth), Z (history other (depth + 1))) ≤
        𝔼 other ∈ pathFiber depth (history reference depth), Z (history other depth)
      have he : (𝔼 other ∈ pathFiber depth (history reference depth), Z (history other (depth + 1))) =
          ∑ c, machineWeight (history reference depth) c * Z (c :: history reference depth) := by
        rw [machineWeight_expectation _ (by
          simpa only [history, profileHistory_length] using pathFiber_nonempty reference depth)]
        simp only [history, profileHistory_length]
        apply Finset.expect_congr rfl
        intro other ho
        have hh := (Finset.mem_filter.mp ho).2
        change profileHistory (liftedProfile other) depth = history reference depth at hh
        simp only [profileHistory_succ, hh]
      have he' : (𝔼 other ∈ pathFiber depth (history reference depth), Z (history other depth)) =
          Z (history reference depth) := by
        calc
          _ = 𝔼 _other ∈ pathFiber depth (history reference depth), Z (history reference depth) := by
            apply Finset.expect_congr rfl
            intro other ho
            rw [(Finset.mem_filter.mp ho).2]
          _ = _ := Finset.expect_const (pathFiber_nonempty reference depth) _
      rw [he, he']
      exact hZ.2 _

theorem profile_weightedArrivalProcess_expectation_le_one
    (X : List (Fin (m * q)) → Fin (m * q) → Bool)
    (z : List (Fin (m * q)) → ℝ) (θ : ℝ) (depth : ℕ) :
    (𝔼 profile ∈ ReplicaPS.profileSample m q,
      weightedArrivalProcess machineWeight X z θ (history profile depth)) ≤ 1 := by
  simpa only [weightedArrivalProcess_nil] using profile_supermartingale_expectation_le
    (weightedArrivalProcess_supermartingale machineWeight_valid X z θ) depth

theorem fresh_answer_probability (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true) (g : Fin m)
    (hg : g ∈ queryTypes (history reference depth)) :
    (𝔼 other ∈ pathFiber depth (history reference depth),
      if typeOf (answer other (history reference depth)) = g then (1 : ℝ) else 0) =
      1 / ((queryTypes (history reference depth)).card : ℝ) := by
  let H := revealHistory reference depth
  let A := queryTypes (history reference depth)
  let i := queryAgent (history reference depth)
  have hA : A.Nonempty := stochastic_nonempty _ hs
  have hC : (compatibleProfiles H).Nonempty :=
    ⟨reference, mem_compatibleProfiles_iff.mpr (revealHistory_compatible _ _)⟩
  rw [pathFiber_eq_compatibleProfiles]
  have he : (𝔼 other ∈ compatibleProfiles H,
      if typeOf (answer other (history reference depth)) = g then (1 : ℝ) else 0) =
      (answerFiber H i A hA g).card / ((compatibleProfiles H).card : ℝ) := by
    calc
      _ = 𝔼 other ∈ compatibleProfiles H,
          if favorite (other i) A hA = g then (1 : ℝ) else 0 := by
        apply Finset.expect_congr rfl
        intro other ho
        have hp := history_eq_of_compatible reference other depth (mem_compatibleProfiles_iff.mp ho)
        have hAo : (queryTypes (history other depth)).Nonempty := by rw [← hp]; exact hA
        have ht := answer_type other depth hAo
        simp only [← hp] at ht
        rw [ht]
      _ = _ := by simp [Finset.expect_eq_sum_div_card, answerFiber]
  rw [he]
  have hc := answerFiber_card_mul_available hA (fresh_query_admissible reference depth hs) hg
  have hcR : ((answerFiber H i A hA g).card : ℝ) * A.card = (compatibleProfiles H).card := by
    exact_mod_cast hc
  have haR : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hCR : (0 : ℝ) < (compatibleProfiles H).card := by exact_mod_cast Finset.card_pos.mpr hC
  change ((answerFiber H i A hA g).card : ℝ) / (compatibleProfiles H).card = 1 / (A.card : ℝ)
  apply (div_eq_div_iff hCR.ne' haR.ne').2
  simpa only [one_mul] using hcR

def entry (g : Fin m) (h : List (Fin (m * q))) (c : Fin (m * q)) : Bool :=
  stochasticRecording h && decide (g ∈ queryTypes h ∧ typeOf c = g)

def arrivalWeight (h : List (Fin (m * q))) : ℝ :=
  if stochasticRecording h then 1 / ((queryTypes h).card : ℝ) else 0

lemma arrivalWeight_nonneg (h : List (Fin (m * q))) : 0 ≤ arrivalWeight h := by
  unfold arrivalWeight
  split <;> positivity

theorem entry_successProbability (profile : ReplicaPS.Profile m q) (depth : ℕ) (g : Fin m)
    (hg : g ∈ queryTypes (history profile depth)) :
    successProbability machineWeight (entry g) (history profile depth) =
      arrivalWeight (history profile depth) := by
  unfold successProbability
  rw [machineWeight_expectation _ (by
    simpa only [history, profileHistory_length] using pathFiber_nonempty profile depth)]
  simp only [history, profileHistory_length]
  by_cases hs : stochasticRecording (history profile depth) = true
  · have h := fresh_answer_probability profile depth hs g hg
    simpa only [entry, hs, Bool.true_and, hg, true_and, decide_eq_true_eq,
      arrivalWeight, Bool.true_eq, if_true] using h
  · have hs' := Bool.eq_false_of_not_eq_true hs
    simp only [entry, hs', Bool.false_and, Bool.false_eq_true, if_false,
      arrivalWeight]
    simp

end ProbabilisticSerial.ReplicaChoiceMachine
