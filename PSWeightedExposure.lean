import PSFiniteCapacity
import FiniteSurvivor
import FiniteAtomicExposure

/-! Weighted arrivals and the exposure envelope for the concrete PS process. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess AdaptiveCategorical SequentialRevelation StoppedChoices
variable {n : ℕ} [Nonempty (Fin n)]

lemma sum_slots (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N * n), f k =
      ∑ r ∈ Finset.range N, ∑ i : Fin n, f (r * n + i.val) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.add_mul, Nat.one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dif_pos (Finset.mem_range.mp hk)]

def timeWeight (t : ℝ) (h : History (Fin n)) : ℝ := max (t - queryTime h) 0

def arrivalWeight (h : History (Fin n)) : ℝ :=
  if stochasticRecording h then 1 / ((queryActive h).card : ℝ) else 0

def profileExposureCost (profile : Profile n) (θ t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range n, ∑ i : Fin n,
    arrivalWeight (profileHistory profile (r * n + i.val)) *
      (1 - Real.exp (-θ * max (t - roundTime profile r) 0))

def profileExposure (profile : Profile n) : ℝ :=
  ∑ r ∈ Finset.range n, ∑ i : Fin n,
    arrivalWeight (profileHistory profile (r * n + i.val)) *
      max (1 - roundTime profile r) 0

lemma arrivalWeight_nonneg (h : History (Fin n)) : 0 ≤ arrivalWeight h := by
  unfold arrivalWeight
  split <;> positivity

lemma entry_successProbability (h : History (Fin n)) (g : Fin n)
    (hg : g ∈ queryActive h) :
    successProbability machineWeight (setEntry {g}) h = arrivalWeight h := by
  change successProbability (uniformChoiceWeight queryAvailable)
    (stoppedEntry {g} (setRecording {g})) h = arrivalWeight h
  rw [uniformChoice_successProbability queryAvailable queryAvailable_nonempty]
  by_cases hs : stochasticRecording h = true
  · have hsub : ({g} : Finset (Fin n)) ⊆ queryActive h := by simpa using hg
    have hrec : setRecording {g} h = true := by simp [setRecording, hs, hsub]
    rw [hrec, if_pos rfl, queryAvailable_eq_active_of_stochastic h hs,
      entryParameter_eq_card_div hsub]
    simp [arrivalWeight, hs]
  · have hs0 := Bool.eq_false_of_not_eq_true hs
    simp [setRecording, hs0, arrivalWeight]

lemma weightedCompensator_eq_exposure (profile : Profile n) (θ t : ℝ) (g : Fin n)
    (hsurvive : ∀ r < n, roundTime profile r < t →
      g ∈ activeGoods (profileSupply profile r)) :
    weightedCompensator machineWeight (setEntry {g}) (timeWeight t) θ
      (profileHistory profile (n * n)) = profileExposureCost profile θ t := by
  rw [weightedCompensator_profileHistory, sum_slots]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  have hz : timeWeight t (profileHistory profile (r * n + i.val)) =
      max (t - roundTime profile r) 0 := by simp [timeWeight, queryTime_at_slot]
  rw [hz]
  by_cases ht : roundTime profile r < t
  · rw [entry_successProbability _ g (by
      rw [queryActive_at_slot]
      exact hsurvive r (Finset.mem_range.mp hr) ht)]
  · simp [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]

def choiceIndicator (profile : Profile n) (i g : Fin n) (r : ℕ) : ℝ :=
  if roundChoice profile r i = g then 1 else 0

lemma sum_choiceIndicator (profile : Profile n) (g : Fin n) (r : ℕ) :
    ∑ i : Fin n, choiceIndicator profile i g r =
      (choiceDemand (roundChoice profile r) g : ℝ) := by
  simp only [choiceIndicator, choiceDemand, choiceConsumers, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma entry_initial_weighted (profile : Profile n) (t : ℝ) (i g : Fin n)
    (hg : g ∈ activeGoods (profileSupply profile 0)) :
    timeWeight t (profileHistory profile i.val) *
      (if setEntry {g} (profileHistory profile i.val)
        (profileAnswer profile (profileHistory profile i.val)) then 1 else 0) =
      max (t - roundTime profile 0) 0 * choiceIndicator profile i g 0 := by
  let hA : (activeGoods (profileSupply profile 0)).Nonempty := ⟨g, hg⟩
  rw [initial_setEntry_eq profile {g} i hA (by simpa using hg)]
  have htime := queryTime_at_slot profile 0 i
  simp only [Nat.zero_mul, Nat.zero_add] at htime
  simp [timeWeight, htime, choiceIndicator, roundChoice_eq profile 0 i hA]

lemma entry_successor_weighted (profile : Profile n) (t : ℝ) (r : ℕ) (i g : Fin n)
    (hsurvive : roundTime profile (r + 1) < t →
      g ∈ activeGoods (profileSupply profile (r + 1))) :
    timeWeight t (profileHistory profile ((r + 1) * n + i.val)) *
      (if setEntry {g} (profileHistory profile ((r + 1) * n + i.val))
        (profileAnswer profile (profileHistory profile ((r + 1) * n + i.val))) then 1 else 0) =
      max (t - roundTime profile (r + 1)) 0 *
        (choiceIndicator profile i g (r + 1) - choiceIndicator profile i g r) := by
  simp only [timeWeight, queryTime_at_slot]
  by_cases ht : roundTime profile (r + 1) < t
  · have hg := hsurvive ht
    let hA : (activeGoods (profileSupply profile (r + 1))).Nonempty := ⟨g, hg⟩
    let hprev : (activeGoods (profileSupply profile r)).Nonempty :=
      ⟨g, profileSupply_active_subset profile r hg⟩
    rw [successor_setEntry_eq profile {g} r i hA (by simpa using hg)]
    simp only [Finset.mem_singleton, decide_eq_true_eq, choiceIndicator,
      roundChoice_eq profile (r + 1) i hA, roundChoice_eq profile r i hprev]
    by_cases hold : favorite (profile i) (activeGoods (profileSupply profile r)) hprev = g
    · have hnew : favorite (profile i) (activeGoods (profileSupply profile (r + 1))) hA = g :=
        (favorite_of_mem_of_subset (profile i) hprev hA
          (profileSupply_active_subset profile r) (hold ▸ hg)).trans hold
      simp [hold, hnew, hg]
    · by_cases hnew : favorite (profile i)
          (activeGoods (profileSupply profile (r + 1))) hA = g
      · have hgone : favorite (profile i) (activeGoods (profileSupply profile r)) hprev ∉
            activeGoods (profileSupply profile (r + 1)) := by
          intro hm
          exact hold ((favorite_of_mem_of_subset (profile i) hprev hA
            (profileSupply_active_subset profile r) hm).symm.trans hnew)
        simp [hold, hnew, hgone]
      · simp [hold, hnew]
  · simp [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]

lemma sum_shifted_entries (z a e : ℕ → ℝ) (N : ℕ)
    (hzero : e 0 = z 0 * a 0)
    (hsucc : ∀ k, e (k + 1) = z (k + 1) * (a (k + 1) - a k))
    (hz : z N = 0) :
    ∑ r ∈ Finset.range N, e r =
      ∑ r ∈ Finset.range N, (z r - z (r + 1)) * a r := by
  have hshift : ∀ N : ℕ,
      (∑ r ∈ Finset.range N, e r) + e N =
        e 0 + ∑ k ∈ Finset.range N, e (k + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => simp only [Finset.sum_range_succ]; linarith
  have heN : e N = 0 := by
    cases N with
    | zero => rw [hzero, hz, zero_mul]
    | succ N => rw [hsucc, hz, zero_mul]
  have h := hshift N
  rw [heN, add_zero, hzero] at h
  simp_rw [hsucc] at h
  exact h.trans (weighted_entries_eq_integral z a N hz)

lemma weightedSuccesses_eq_consumption (profile : Profile n) (t : ℝ) (ht : t ≤ 1)
    (g : Fin n) (hsurvive : ∀ r < n, roundTime profile r < t →
      g ∈ activeGoods (profileSupply profile r)) :
    weightedSuccesses (setEntry {g}) (timeWeight t)
      (profileHistory profile (n * n)) = partialConsumption profile t g := by
  classical
  have hsurviveAll (r : ℕ) (hr : roundTime profile r < t) :
      g ∈ activeGoods (profileSupply profile r) := by
    by_cases hrn : r < n
    · exact hsurvive r hrn hr
    · have hmono := roundTime_mono profile (Nat.le_of_not_gt hrn)
      rw [roundTime_terminal] at hmono
      linarith
  have hinit : g ∈ activeGoods (profileSupply profile 0) := by
    simp [profileSupply, activeGoods_initial]
  rw [weightedSuccesses_profileHistory, sum_slots, Finset.sum_comm]
  have heach (i : Fin n) :
      (∑ r ∈ Finset.range n, timeWeight t (profileHistory profile (r * n + i.val)) *
        (if setEntry {g} (profileHistory profile (r * n + i.val))
          (profileAnswer profile (profileHistory profile (r * n + i.val))) then 1 else 0)) =
        ∑ r ∈ Finset.range n, partialDuration profile t r * choiceIndicator profile i g r := by
    have h := sum_shifted_entries
      (fun r => max (t - roundTime profile r) 0) (choiceIndicator profile i g)
      (fun r => timeWeight t (profileHistory profile (r * n + i.val)) *
        (if setEntry {g} (profileHistory profile (r * n + i.val))
          (profileAnswer profile (profileHistory profile (r * n + i.val))) then 1 else 0)) n
      (by simpa using entry_initial_weighted profile t i g hinit)
      (fun r => entry_successor_weighted profile t r i g (hsurviveAll (r + 1)))
      (by
        change max (t - roundTime profile n) 0 = 0
        rw [roundTime_terminal, max_eq_right (sub_nonpos.mpr ht)])
    simpa only [← partialDuration_eq_ramp] using h
  simp_rw [heach]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_choiceIndicator]
  rfl

end ProbabilisticSerial.PSChoiceMachine
