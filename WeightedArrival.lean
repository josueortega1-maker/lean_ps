import PSChoiceMachine

/-!
# Predictable weighted arrivals on the actual PS revelation tree

The finite-expectation argument uses a different exponential process from the
unweighted load bound: each choice has a weight determined by the history
before that choice. This file proves its one-step inequality and its finite
expectation bound, then transfers that bound to uniform preference profiles.

The weights may include a deterministic time horizon and predictable stopping.
Identifying them with the continuous-time capacity and exposure statistics is
a separate process identity; no such identity is assumed here.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.AdaptiveCategorical

def weightedSuccesses {α : Type*} (X : History α → α → Bool)
    (z : History α → ℝ) : History α → ℝ
  | [] => 0
  | a :: h => weightedSuccesses X z h + z h * if X h a then 1 else 0

def weightedCompensator {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (z : History α → ℝ) (θ : ℝ) : History α → ℝ
  | [] => 0
  | _a :: h => weightedCompensator weight X z θ h +
      successProbability weight X h * (1 - Real.exp (-θ * z h))

/-- The exponential process in equation `finite-martingale` of the manuscript.
The weight `z h` depends only on the past, not on the next answer. -/
def weightedArrivalProcess {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (z : History α → ℝ) (θ : ℝ) (h : History α) : ℝ :=
  Real.exp (-θ * weightedSuccesses X z h + weightedCompensator weight X z θ h)

@[simp] lemma weightedArrivalProcess_nil {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (z : History α → ℝ) (θ : ℝ) :
    weightedArrivalProcess weight X z θ [] = 1 := by
  simp [weightedArrivalProcess, weightedSuccesses, weightedCompensator]

/-- The estimate holds for arbitrary real predictable weights and parameters;
the paper uses nonnegative time weights and a positive parameter. -/
theorem weightedArrivalProcess_supermartingale {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) (z : History α → ℝ) (θ : ℝ) :
    IsTreeSupermartingale weight (weightedArrivalProcess weight X z θ) := by
  constructor
  · intro h
    exact (Real.exp_pos _).le
  · intro h
    let β := -θ * z h
    let r := successProbability weight X h * (Real.exp β - 1)
    have hchild (a : α) :
        weightedArrivalProcess weight X z θ (a :: h) =
          weightedArrivalProcess weight X z θ h *
            Real.exp (β * (if X h a then 1 else 0) - r) := by
      simp only [weightedArrivalProcess, weightedSuccesses, weightedCompensator]
      rw [← Real.exp_add]
      congr 1
      dsimp [β, r]
      ring
    simp_rw [hchild]
    calc
      (∑ a, weight h a * (weightedArrivalProcess weight X z θ h *
          Real.exp (β * (if X h a then 1 else 0) - r))) =
          weightedArrivalProcess weight X z θ h * Real.exp (-r) *
            (∑ a, weight h a * Real.exp (β * (if X h a then 1 else 0))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [show Real.exp (β * (if X h a then 1 else 0) - r) =
          Real.exp (-r) * Real.exp (β * (if X h a then 1 else 0)) by
            rw [← Real.exp_add]
            congr 1 <;> ring]
        ring
      _ = weightedArrivalProcess weight X z θ h *
          (Real.exp (-r) * (1 + r)) := by
        rw [weighted_exp_bool hweight X β h]
        dsimp [r]
        ring
      _ ≤ weightedArrivalProcess weight X z θ h * 1 :=
        mul_le_mul_of_nonneg_left
          (AdaptiveBernoulli.exp_neg_mul_one_add_le_one r) (Real.exp_pos _).le
      _ = weightedArrivalProcess weight X z θ h := mul_one _

/-- Finite-horizon expectation of any tree supermartingale. -/
theorem sequence_expectation_le {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    {Z : History α → ℝ} (hZ : IsTreeSupermartingale weight Z) :
    ∀ depth h,
      (∑ labels, PSChoiceMachine.sequenceWeight weight depth h labels *
        Z (PSChoiceMachine.followSequence depth h labels)) ≤ Z h := by
  intro depth
  induction depth with
  | zero =>
      intro h
      simp [PSChoiceMachine.sequenceWeight, PSChoiceMachine.followSequence]
  | succ depth ih =>
      intro h
      rw [PSChoiceMachine.sum_fin_sequence_succ]
      simp only [PSChoiceMachine.sequenceWeight, PSChoiceMachine.followSequence,
        Fin.cons_zero, Fin.tail_cons]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      calc
        _ ≤ ∑ a, weight h a * Z (a :: h) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (ih _) ((hweight h).1 a)
        _ ≤ Z h := hZ.2 h

theorem weightedArrivalProcess_expectation_le_one {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) (z : History α → ℝ) (θ : ℝ) (depth : ℕ) :
    (∑ labels, PSChoiceMachine.sequenceWeight weight depth [] labels *
      weightedArrivalProcess weight X z θ
        (PSChoiceMachine.followSequence depth [] labels)) ≤ 1 := by
  simpa using sequence_expectation_le hweight
    (weightedArrivalProcess_supermartingale hweight X z θ) depth []

end ProbabilisticSerial.AdaptiveCategorical

namespace ProbabilisticSerial.PSChoiceMachine

open AdaptiveCategorical UniformPermutation PSProcess

variable {n : ℕ} [Nonempty (Fin n)]

/-- The existing exact-path fiber bound also controls arbitrary nonnegative
terminal statistics, without a persistence condition on an event. -/
theorem profile_terminal_expectation_le_sequence_sum
    (Z : History (Fin n) → ℝ) (hZ : ∀ h, 0 ≤ Z h) (depth : ℕ) :
    (𝔼 profile ∈ preferenceProfileSample n, Z (profileHistory profile depth)) ≤
      ∑ labels, sequenceWeight (machineWeight (n := n)) depth [] labels *
        Z (followSequence depth [] labels) := by
  have hpartition := Finset.sum_fiberwise (preferenceProfileSample n)
    (fun profile => profileLabels profile depth)
    (fun profile => Z (profileHistory profile depth))
  have hfiber (labels : Fin depth → Fin n) :
      (∑ profile ∈ profileLabelFiber depth labels, Z (profileHistory profile depth)) =
        ((profileLabelFiber depth labels).card : ℝ) *
          Z (followSequence depth [] labels) := by
    calc
      _ = ∑ _profile ∈ profileLabelFiber depth labels,
          Z (followSequence depth [] labels) := by
        apply Finset.sum_congr rfl
        intro profile hprofile
        have hlabels := (Finset.mem_filter.mp hprofile).2
        rw [← followSequence_profileLabels profile depth, hlabels]
      _ = _ := by simp
  rw [Finset.expect_eq_sum_div_card, ← hpartition, Finset.sum_div]
  apply Finset.sum_le_sum
  intro labels hlabels
  change (∑ profile ∈ profileLabelFiber depth labels,
      Z (profileHistory profile depth)) / (preferenceProfileSample n).card ≤ _
  rw [hfiber, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right
    (profileLabelFiber_probability_le_sequenceWeight depth labels) (hZ _)

theorem profile_supermartingale_expectation_le
    (Z : History (Fin n) → ℝ)
    (hZ : IsTreeSupermartingale (machineWeight (n := n)) Z) (depth : ℕ) :
    (𝔼 profile ∈ preferenceProfileSample n, Z (profileHistory profile depth)) ≤ Z [] :=
  (profile_terminal_expectation_le_sequence_sum Z hZ.1 depth).trans
    (sequence_expectation_le machineWeight_valid hZ depth [])

/-- Equation `finite-martingale` on the genuine uniform one-copy PS profiles,
for any predictable weights, any recorded Boolean entries, and any finite depth.
The law-transfer assumption is discharged by the existing permutation proof. -/
theorem profile_weightedArrivalProcess_expectation_le_one
    (X : History (Fin n) → Fin n → Bool) (z : History (Fin n) → ℝ)
    (θ : ℝ) (depth : ℕ) :
    (𝔼 profile ∈ preferenceProfileSample n,
      weightedArrivalProcess machineWeight X z θ (profileHistory profile depth)) ≤ 1 := by
  simpa using profile_supermartingale_expectation_le
    (weightedArrivalProcess machineWeight X z θ)
    (weightedArrivalProcess_supermartingale machineWeight_valid X z θ) depth

end ProbabilisticSerial.PSChoiceMachine
