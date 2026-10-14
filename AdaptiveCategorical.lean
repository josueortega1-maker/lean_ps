import AdaptiveBernoulli

/-!
# Adaptive Bernoulli concentration with labelled side information

The binary history in `AdaptiveBernoulli` is enough when the transition
probability is determined by earlier success bits.  Sequential revelation in
probabilistic serial has a richer filtration: identities of earlier goods and
agents determine the next available set.  This file proves the same finite-tree
Ville bounds on histories with arbitrary finite labels.  A Boolean function of
each labelled transition is the Bernoulli observation, while the entire label
is retained as side information.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.AdaptiveCategorical

abbrev History (α : Type*) := List α

/-- Transition weights on a finite labelled tree. Histories are stored newest
first, so the children of `h` are `a :: h`. -/
def ValidLaw {α : Type*} [Fintype α] (weight : History α → α → ℝ) : Prop :=
  ∀ h, (∀ a, 0 ≤ weight h a) ∧ ∑ a, weight h a = 1

/-- Conditional probability of the Boolean event on the next labelled edge. -/
def successProbability {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (h : History α) : ℝ :=
  ∑ a, weight h a * if X h a then 1 else 0

def successes {α : Type*} (X : History α → α → Bool) :
    History α → ℝ
  | [] => 0
  | a :: h => successes X h + if X h a then 1 else 0

def compensator {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool) :
    History α → ℝ
  | [] => 0
  | _a :: h => compensator weight X h + successProbability weight X h

@[simp] lemma successes_nil {α : Type*} (X : History α → α → Bool) :
    successes X [] = 0 := rfl

@[simp] lemma successes_cons {α : Type*} (X : History α → α → Bool)
    (h : History α) (a : α) :
    successes X (a :: h) = successes X h + if X h a then 1 else 0 := rfl

@[simp] lemma compensator_nil {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool) :
    compensator weight X [] = 0 := rfl

@[simp] lemma compensator_cons {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (h : History α) (a : α) :
    compensator weight X (a :: h) =
      compensator weight X h + successProbability weight X h := rfl

def hitProbability {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (event : History α → Prop)
    [DecidablePred event] : ℕ → History α → ℝ
  | 0, h => if event h then 1 else 0
  | depth + 1, h =>
      if event h then 1
      else ∑ a, weight h a * hitProbability weight event depth (a :: h)

def IsTreeSupermartingale {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (Z : History α → ℝ) : Prop :=
  (∀ h, 0 ≤ Z h) ∧
    ∀ h, (∑ a, weight h a * Z (a :: h)) ≤ Z h

lemma hitProbability_nonneg {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (event : History α → Prop) [DecidablePred event] :
    ∀ depth h, 0 ≤ hitProbability weight event depth h := by
  intro depth
  induction depth with
  | zero =>
      intro h
      simp only [hitProbability]
      split_ifs <;> norm_num
  | succ depth ih =>
      intro h
      simp only [hitProbability]
      split_ifs
      · norm_num
      · exact Finset.sum_nonneg fun a ha =>
          mul_nonneg ((hweight h).1 a) (ih _)

lemma threshold_mul_hitProbability_le {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    {Z : History α → ℝ} (hZ : IsTreeSupermartingale weight Z)
    {event : History α → Prop} [DecidablePred event]
    {threshold : ℝ}
    (h_event : ∀ h, event h → threshold ≤ Z h) :
    ∀ depth h,
      threshold * hitProbability weight event depth h ≤ Z h := by
  intro depth
  induction depth with
  | zero =>
      intro h
      simp only [hitProbability]
      by_cases he : event h
      · simp [he, h_event h he]
      · simp [he, hZ.1 h]
  | succ depth ih =>
      intro h
      simp only [hitProbability]
      by_cases he : event h
      · simp [he, h_event h he]
      · rw [if_neg he, Finset.mul_sum]
        calc
          (∑ a, threshold *
              (weight h a * hitProbability weight event depth (a :: h))) =
              ∑ a, weight h a *
                (threshold * hitProbability weight event depth (a :: h)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ ≤ ∑ a, weight h a * Z (a :: h) := by
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (ih _)
              ((hweight h).1 a)
          _ ≤ Z h := hZ.2 h

lemma hitProbability_le_inv {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    {Z : History α → ℝ} (hZ : IsTreeSupermartingale weight Z)
    {event : History α → Prop} [DecidablePred event]
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (h_event : ∀ h, event h → threshold ≤ Z h)
    (depth : ℕ) (h : History α) :
    hitProbability weight event depth h ≤ Z h / threshold := by
  rw [le_div_iff₀ hthreshold]
  simpa [mul_comm] using threshold_mul_hitProbability_le hweight hZ
    h_event depth h

def upperProcess {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (θ : ℝ) (h : History α) : ℝ :=
  Real.exp (θ * successes X h -
    (Real.exp θ - 1) * compensator weight X h)

def lowerProcess {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (θ : ℝ) (h : History α) : ℝ :=
  Real.exp (-θ * successes X h +
    (1 - Real.exp (-θ)) * compensator weight X h)

lemma weighted_exp_bool {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) (θ : ℝ) (h : History α) :
    (∑ a, weight h a *
      Real.exp (θ * (if X h a then 1 else 0))) =
      1 + successProbability weight X h * (Real.exp θ - 1) := by
  calc
    (∑ a, weight h a *
      Real.exp (θ * (if X h a then 1 else 0))) =
        ∑ a, (weight h a +
          (weight h a * (if X h a then 1 else 0)) *
            (Real.exp θ - 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      cases hx : X h a <;> simp [hx] <;> ring
    _ = (∑ a, weight h a) +
        (∑ a, weight h a * (if X h a then 1 else 0)) *
          (Real.exp θ - 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = 1 + successProbability weight X h * (Real.exp θ - 1) := by
      rw [(hweight h).2]
      rfl

lemma upperProcess_supermartingale {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) (θ : ℝ) :
    IsTreeSupermartingale weight (upperProcess weight X θ) := by
  constructor
  · intro h
    exact (Real.exp_pos _).le
  · intro h
    let p := successProbability weight X h
    let q := Real.exp θ - 1
    let z := p * q
    have hchild (a : α) :
        upperProcess weight X θ (a :: h) =
          upperProcess weight X θ h *
            Real.exp (θ * (if X h a then 1 else 0) - z) := by
      simp only [upperProcess, successes_cons, compensator_cons]
      rw [← Real.exp_add]
      congr 1
      dsimp [p, q, z]
      ring
    simp_rw [hchild]
    calc
      (∑ a, weight h a *
        (upperProcess weight X θ h *
          Real.exp (θ * (if X h a then 1 else 0) - z))) =
          upperProcess weight X θ h * Real.exp (-z) *
            (∑ a, weight h a *
              Real.exp (θ * (if X h a then 1 else 0))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [show Real.exp (θ * (if X h a then 1 else 0) - z) =
          Real.exp (-z) *
            Real.exp (θ * (if X h a then 1 else 0)) by
              rw [← Real.exp_add]
              congr 1 <;> ring]
        ring
      _ = upperProcess weight X θ h *
          (Real.exp (-z) * (1 + z)) := by
        rw [weighted_exp_bool hweight X θ h]
        dsimp [z, p, q]
        ring
      _ ≤ upperProcess weight X θ h * 1 :=
        mul_le_mul_of_nonneg_left
          (AdaptiveBernoulli.exp_neg_mul_one_add_le_one z)
          (Real.exp_pos _).le
      _ = upperProcess weight X θ h := mul_one _

lemma lowerProcess_eq_upperProcess_neg {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (θ : ℝ) (h : History α) :
    lowerProcess weight X θ h = upperProcess weight X (-θ) h := by
  simp only [lowerProcess, upperProcess]
  ring_nf

lemma lowerProcess_supermartingale {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) (θ : ℝ) :
    IsTreeSupermartingale weight (lowerProcess weight X θ) := by
  rw [show lowerProcess weight X θ = upperProcess weight X (-θ) by
    funext h
    exact lowerProcess_eq_upperProcess_neg weight X θ h]
  exact upperProcess_supermartingale hweight X (-θ)

@[simp] lemma upperProcess_nil {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool) (θ : ℝ) :
    upperProcess weight X θ [] = 1 := by
  simp [upperProcess]

@[simp] lemma lowerProcess_nil {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool) (θ : ℝ) :
    lowerProcess weight X θ [] = 1 := by
  simp [lowerProcess]

theorem upper_deviation {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool)
    {x v : ℝ} (hxv : v < x) (hv : 0 < v) (depth : ℕ) :
    hitProbability weight
        (fun h => x ≤ successes X h ∧ compensator weight X h ≤ v)
        depth [] ≤
      Real.exp (-x * Real.log (x / v) + x - v) := by
  let θ := Real.log (x / v)
  let threshold := Real.exp (x * Real.log (x / v) - x + v)
  have hvx : 0 < x := hv.trans hxv
  have hratio : 0 < x / v := div_pos hvx hv
  have hexpθ : Real.exp θ = x / v := by
    dsimp [θ]
    exact Real.exp_log hratio
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    apply Real.log_nonneg
    apply (le_div_iff₀ hv).2
    simpa using hxv.le
  have hthreshold : 0 < threshold := Real.exp_pos _
  have hevent : ∀ h,
      (x ≤ successes X h ∧ compensator weight X h ≤ v) →
        threshold ≤ upperProcess weight X θ h := by
    intro h hh
    apply Real.exp_le_exp.mpr
    change x * Real.log (x / v) - x + v ≤
      θ * successes X h -
        (Real.exp θ - 1) * compensator weight X h
    rw [hexpθ]
    have hq : 0 ≤ x / v - 1 := by
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hv).2
      simpa using hxv.le
    calc
      x * Real.log (x / v) - x + v =
          θ * x - (x / v - 1) * v := by
        dsimp [θ]
        field_simp
        ring
      _ ≤ θ * successes X h -
          (x / v - 1) * compensator weight X h := by
        exact sub_le_sub
          (mul_le_mul_of_nonneg_left hh.1 hθ)
          (mul_le_mul_of_nonneg_left hh.2 hq)
  have hville := hitProbability_le_inv hweight
    (upperProcess_supermartingale hweight X θ)
    hthreshold hevent depth []
  rw [upperProcess_nil] at hville
  calc
    hitProbability weight
        (fun h => x ≤ successes X h ∧ compensator weight X h ≤ v)
        depth [] ≤ 1 / threshold := hville
    _ = Real.exp (-x * Real.log (x / v) + x - v) := by
      dsimp [threshold]
      rw [one_div, ← Real.exp_neg]
      congr 1 <;> ring

theorem lower_deviation {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (X : History α → α → Bool) {v : ℝ} (hv : 0 ≤ v)
    (depth : ℕ) :
    hitProbability weight
        (fun h => v ≤ compensator weight X h ∧
          successes X h ≤ compensator weight X h / 4)
        depth [] ≤
      Real.exp (-AdaptiveBernoulli.lowerRate * v) := by
  let θ := Real.log 2
  let threshold := Real.exp (AdaptiveBernoulli.lowerRate * v)
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact Real.log_nonneg (by norm_num)
  have hexpneg : Real.exp (-θ) = (1 : ℝ) / 2 := by
    dsimp [θ]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthreshold : 0 < threshold := Real.exp_pos _
  have hevent : ∀ h,
      (v ≤ compensator weight X h ∧
        successes X h ≤ compensator weight X h / 4) →
        threshold ≤ lowerProcess weight X θ h := by
    intro h hh
    apply Real.exp_le_exp.mpr
    change AdaptiveBernoulli.lowerRate * v ≤
      -θ * successes X h +
        (1 - Real.exp (-θ)) * compensator weight X h
    rw [hexpneg]
    have hcomp : 0 ≤ compensator weight X h := hv.trans hh.1
    calc
      AdaptiveBernoulli.lowerRate * v ≤
          AdaptiveBernoulli.lowerRate * compensator weight X h :=
        mul_le_mul_of_nonneg_left hh.1 AdaptiveBernoulli.lowerRate_pos.le
      _ = -(Real.log 2) * (compensator weight X h / 4) +
          (1 - (1 : ℝ) / 2) * compensator weight X h := by
        dsimp [AdaptiveBernoulli.lowerRate]
        ring
      _ ≤ -θ * successes X h +
          (1 - (1 : ℝ) / 2) * compensator weight X h := by
        apply add_le_add_right
        exact mul_le_mul_of_nonpos_left hh.2 (neg_nonpos.mpr hθ)
  have hville := hitProbability_le_inv hweight
    (lowerProcess_supermartingale hweight X θ)
    hthreshold hevent depth []
  rw [lowerProcess_nil] at hville
  calc
    hitProbability weight
        (fun h => v ≤ compensator weight X h ∧
          successes X h ≤ compensator weight X h / 4)
        depth [] ≤ 1 / threshold := hville
    _ = Real.exp (-AdaptiveBernoulli.lowerRate * v) := by
      dsimp [threshold]
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

end ProbabilisticSerial.AdaptiveCategorical
