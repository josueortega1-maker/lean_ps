import StoppedChoices
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The union bounds in the PS load proposition

This file formalizes the probabilistic and combinatorial core of Proposition
`load-bound` in the paper.  It proves finite-tree union bounds for the labelled
adaptive law of `AdaptiveCategorical`, specializes both stopped-choice
deviation estimates with the paper's rate function, counts all candidate sets,
and proves the deterministic conversion from few underloaded goods to a demand
lower bound.

The histories retain all revealed labels.  Thus the union is over fixed
candidate sets; no conditioning on an endogenous active set occurs.
-/

noncomputable section

open Finset
open Filter
open scoped BigOperators
open scoped Topology

namespace ProbabilisticSerial.LoadBound

open AdaptiveCategorical StoppedChoices

/-! ## Finite-tree union bounds -/

lemma hitProbability_le_one {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (event : History α → Prop) [DecidablePred event] :
    ∀ depth history, hitProbability weight event depth history ≤ 1 := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp only [hitProbability]
      split_ifs <;> norm_num
  | succ depth ih =>
      intro history
      simp only [hitProbability]
      by_cases hevent : event history
      · simp [hevent]
      · rw [if_neg hevent]
        calc
          (∑ a, weight history a *
              hitProbability weight event depth (a :: history)) ≤
              ∑ a, weight history a * 1 := by
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (ih (a :: history))
              ((hweight history).1 a)
          _ = 1 := by simp [(hweight history).2]

lemma hitProbability_false {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) :
    ∀ depth history,
      hitProbability weight (fun _h => False) depth history = 0 := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp [hitProbability]
  | succ depth ih =>
      intro history
      simp [hitProbability, ih]

lemma hitProbability_mono {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (event₁ event₂ : History α → Prop)
    [DecidablePred event₁] [DecidablePred event₂]
    (hsub : ∀ history, event₁ history → event₂ history) :
    ∀ depth history,
      hitProbability weight event₁ depth history ≤
        hitProbability weight event₂ depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp only [hitProbability]
      by_cases h₁ : event₁ history
      · simp [h₁, hsub history h₁]
      · by_cases h₂ : event₂ history <;> simp [h₁, h₂]
  | succ depth ih =>
      intro history
      simp only [hitProbability]
      by_cases h₁ : event₁ history
      · simp [h₁, hsub history h₁]
      · rw [if_neg h₁]
        by_cases h₂ : event₂ history
        · rw [if_pos h₂]
          have hle := hitProbability_le_one hweight event₁ (depth + 1) history
          simpa only [hitProbability, if_neg h₁] using hle
        · rw [if_neg h₂]
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (ih (a :: history))
            ((hweight history).1 a)

lemma hitProbability_or_le {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (event₁ event₂ : History α → Prop)
    [DecidablePred event₁] [DecidablePred event₂] :
    ∀ depth history,
      hitProbability weight (fun h => event₁ h ∨ event₂ h) depth history ≤
        hitProbability weight event₁ depth history +
          hitProbability weight event₂ depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp only [hitProbability]
      by_cases h₁ : event₁ history <;>
        by_cases h₂ : event₂ history <;> simp [h₁, h₂]
  | succ depth ih =>
      intro history
      simp only [hitProbability]
      by_cases h₁ : event₁ history
      · rw [if_pos (Or.inl h₁), if_pos h₁]
        exact le_add_of_nonneg_right
          (hitProbability_nonneg hweight event₂ (depth + 1) history)
      · rw [if_neg h₁]
        by_cases h₂ : event₂ history
        · rw [if_pos (Or.inr h₂), if_pos h₂]
          have hnonneg :=
            hitProbability_nonneg hweight event₁ (depth + 1) history
          rw [hitProbability, if_neg h₁] at hnonneg
          exact le_add_of_nonneg_left hnonneg
        · rw [if_neg (not_or_intro h₁ h₂), if_neg h₂]
          calc
            (∑ a, weight history a *
                hitProbability weight (fun h => event₁ h ∨ event₂ h)
                  depth (a :: history)) ≤
                ∑ a, weight history a *
                  (hitProbability weight event₁ depth (a :: history) +
                    hitProbability weight event₂ depth (a :: history)) := by
              apply Finset.sum_le_sum
              intro a ha
              exact mul_le_mul_of_nonneg_left (ih (a :: history))
                ((hweight history).1 a)
            _ = (∑ a, weight history a *
                  hitProbability weight event₁ depth (a :: history)) +
                ∑ a, weight history a *
                  hitProbability weight event₂ depth (a :: history) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro a ha
              ring

/-- The event that at least one member of a finite fixed family occurs. -/
def finiteUnionEvent {α ι : Type*} (indices : Finset ι)
    (event : ι → History α → Prop) (history : History α) : Prop :=
  ∃ i ∈ indices, event i history

instance finiteUnionEvent_decidable {α ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (event : ι → History α → Prop)
    [∀ i, DecidablePred (event i)] :
    DecidablePred (finiteUnionEvent indices event) := by
  intro history
  unfold finiteUnionEvent
  infer_instance

lemma hitProbability_finiteUnion_le_sum {α ι : Type*}
    [Fintype α] [DecidableEq ι]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (indices : Finset ι) (event : ι → History α → Prop)
    [∀ i, DecidablePred (event i)] (depth : ℕ) (history : History α) :
    hitProbability weight (finiteUnionEvent indices event) depth history ≤
      ∑ i ∈ indices, hitProbability weight (event i) depth history := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      have hsub : ∀ h, finiteUnionEvent (∅ : Finset ι) event h → False := by
        intro h hh
        simp [finiteUnionEvent] at hh
      calc
        hitProbability weight (finiteUnionEvent (∅ : Finset ι) event)
            depth history ≤
            hitProbability weight (fun _h => False) depth history :=
          hitProbability_mono hweight _ _ hsub depth history
        _ = 0 := hitProbability_false weight depth history
  | @insert i indices hi ih =>
      have hsub : ∀ h, finiteUnionEvent (insert i indices) event h →
          event i h ∨ finiteUnionEvent indices event h := by
        intro h hh
        simpa [finiteUnionEvent, hi] using hh
      calc
        hitProbability weight (finiteUnionEvent (insert i indices) event)
              depth history ≤
            hitProbability weight
              (fun h => event i h ∨ finiteUnionEvent indices event h)
              depth history :=
          hitProbability_mono hweight _ _ hsub depth history
        _ ≤
            hitProbability weight (event i) depth history +
              hitProbability weight (finiteUnionEvent indices event)
                depth history :=
          hitProbability_or_le hweight (event i)
            (finiteUnionEvent indices event) depth history
        _ ≤ hitProbability weight (event i) depth history +
              ∑ j ∈ indices,
                hitProbability weight (event j) depth history :=
          add_le_add_left ih _
        _ = ∑ j ∈ insert i indices,
              hitProbability weight (event j) depth history := by
          simp [hi]

theorem hitProbability_finiteUnion_le_card_mul {α ι : Type*}
    [Fintype α] [DecidableEq ι]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (indices : Finset ι) (event : ι → History α → Prop)
    [∀ i, DecidablePred (event i)] (depth : ℕ) (history : History α)
    (q : ℝ)
    (hfixed : ∀ i ∈ indices,
      hitProbability weight (event i) depth history ≤ q) :
    hitProbability weight (finiteUnionEvent indices event) depth history ≤
      (indices.card : ℝ) * q := by
  calc
    hitProbability weight (finiteUnionEvent indices event) depth history ≤
        ∑ i ∈ indices, hitProbability weight (event i) depth history :=
      hitProbability_finiteUnion_le_sum hweight indices event depth history
    _ ≤ ∑ _i ∈ indices, q := by
      apply Finset.sum_le_sum
      intro i hi
      exact hfixed i hi
    _ = (indices.card : ℝ) * q := by simp

/-! ## The two stopped deviation estimates with the paper's constants -/

/-- The Poisson upper-tail rate used in Step 1 of the load proof. -/
def rateFunction (u : ℝ) : ℝ := Real.log (1 / u) - 1 + u

theorem stoppedChoice_potential_deviation {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : History (Fin n) → Bool)
    {η : ℝ} (hηpos : 0 < η) (hηlt : η < 1)
    (hn : 0 < n) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (fun h => (n : ℝ) ≤ successes (stoppedEntry B recording) h ∧
          compensator (uniformChoiceWeight available)
            (stoppedEntry B recording) h ≤ η * (n : ℝ))
        depth [] ≤
      Real.exp (-rateFunction η * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 < η * (n : ℝ) := mul_pos hηpos hnR
  have hxv : η * (n : ℝ) < (n : ℝ) := by
    nlinarith
  have hratio : (n : ℝ) / (η * (n : ℝ)) = 1 / η := by
    field_simp
    ring
  have hbound := stoppedChoice_upper_deviation available hnonempty B
    recording hxv hv depth
  rw [hratio] at hbound
  convert hbound using 1
  unfold rateFunction
  ring

/-- An underload event stated with a fixed lower threshold for the
compensator.  It is contained in the canonical stopped lower-deviation event. -/
def fixedUnderloadEvent {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (v : ℝ) (history : History α) : Prop :=
  v ≤ compensator weight X history ∧ successes X history < v / 4

instance fixedUnderloadEvent_decidable {α : Type*} [Fintype α]
    (weight : History α → α → ℝ) (X : History α → α → Bool)
    (v : ℝ) : DecidablePred (fixedUnderloadEvent weight X v) := by
  intro history
  unfold fixedUnderloadEvent
  infer_instance

theorem stoppedChoice_fixed_underload {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : History (Fin n) → Bool)
    {v : ℝ} (hv : 0 ≤ v) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (fixedUnderloadEvent (uniformChoiceWeight available)
          (stoppedEntry B recording) v) depth [] ≤
      Real.exp (-AdaptiveBernoulli.lowerRate * v) := by
  let weight := uniformChoiceWeight available
  let X := stoppedEntry B recording
  let canonical : History (Fin n) → Prop := fun h =>
    v ≤ compensator weight X h ∧
      successes X h ≤ compensator weight X h / 4
  have hsub : ∀ h,
      fixedUnderloadEvent weight X v h → canonical h := by
    intro h hh
    refine ⟨hh.1, ?_⟩
    have hquarter : v / 4 ≤ compensator weight X h / 4 := by
      exact div_le_div_of_nonneg_right hh.1 (by norm_num)
    exact hh.2.le.trans hquarter
  calc
    hitProbability weight (fixedUnderloadEvent weight X v) depth [] ≤
        hitProbability weight canonical depth [] :=
      hitProbability_mono (uniformChoiceWeight_valid available hnonempty)
        _ _ hsub depth []
    _ ≤ Real.exp (-AdaptiveBernoulli.lowerRate * v) := by
      exact stoppedChoice_lower_deviation available hnonempty B recording hv depth

/-- The exact fixed-`B` exponent in the paper, with
`β = lowerRate * η`. -/
theorem stoppedChoice_fixed_set_exponent {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (B : Finset (Fin n))
    (recording : History (Fin n) → Bool)
    {η lam : ℝ} (hη : 0 ≤ η) (hlam : 0 ≤ lam) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (fixedUnderloadEvent (uniformChoiceWeight available)
          (stoppedEntry B recording) (η * (B.card : ℝ) * lam))
        depth [] ≤
      Real.exp (-(AdaptiveBernoulli.lowerRate * η) *
        (B.card : ℝ) * lam) := by
  have hv : 0 ≤ η * (B.card : ℝ) * lam := by positivity
  convert stoppedChoice_fixed_underload available hnonempty B recording hv depth
    using 1
  all_goals ring

/-! ## Union over all fixed candidate sets -/

def potentialFailureEvent {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (η : ℝ) (S : Finset (Fin n)) (history : History (Fin n)) : Prop :=
  (n : ℝ) ≤ successes (stoppedEntry S (recording S)) history ∧
    compensator (uniformChoiceWeight available)
      (stoppedEntry S (recording S)) history ≤ η * (n : ℝ)

instance potentialFailureEvent_decidable {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (η : ℝ) (S : Finset (Fin n)) :
    DecidablePred (potentialFailureEvent available recording η S) := by
  intro history
  unfold potentialFailureEvent
  infer_instance

/-- Step 1's union bound over all at most `2^n` possible active sets. -/
theorem allSet_potential_union_bound {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    {η : ℝ} (hηpos : 0 < η) (hηlt : η < 1)
    (hn : 0 < n) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (Finset.univ.powerset)
          (potentialFailureEvent available recording η)) depth [] ≤
      (2 : ℝ) ^ n * Real.exp (-rateFunction η * (n : ℝ)) := by
  have hvalid := uniformChoiceWeight_valid available hnonempty
  have hfixed : ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      hitProbability (uniformChoiceWeight available)
          (potentialFailureEvent available recording η S) depth [] ≤
        Real.exp (-rateFunction η * (n : ℝ)) := by
    intro S hS
    exact stoppedChoice_potential_deviation available hnonempty S
      (recording S) hηpos hηlt hn depth
  have hunion := hitProbability_finiteUnion_le_card_mul hvalid
    (Finset.univ.powerset : Finset (Finset (Fin n)))
    (potentialFailureEvent available recording η) depth []
    (Real.exp (-rateFunction η * (n : ℝ))) hfixed
  simpa [Finset.card_powerset, Nat.cast_pow] using hunion

/-- After `I(η) > log 2`, the first union bound remains exponentially small. -/
theorem allSet_potential_exponential_bound {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    {η : ℝ} (hηpos : 0 < η) (hηlt : η < 1)
    (hn : 0 < n) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (Finset.univ.powerset)
          (potentialFailureEvent available recording η)) depth [] ≤
      Real.exp (-(rateFunction η - Real.log 2) * (n : ℝ)) := by
  have hbound := allSet_potential_union_bound available hnonempty recording
    hηpos hηlt hn depth
  have htwo : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (Finset.univ.powerset)
          (potentialFailureEvent available recording η)) depth [] ≤
        (2 : ℝ) ^ n * Real.exp (-rateFunction η * (n : ℝ)) := hbound
    _ = Real.exp (-(rateFunction η - Real.log 2) * (n : ℝ)) := by
      rw [← htwo, ← Real.exp_add]
      congr 1
      ring

/-- The candidate `b`-subsets used in Step 3. -/
def candidateSets (n b : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard b

def fixedSetUnderloadFamily {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (η lam : ℝ) (B : Finset (Fin n)) : History (Fin n) → Prop :=
  fixedUnderloadEvent (uniformChoiceWeight available)
    (stoppedEntry B (recording B)) (η * (B.card : ℝ) * lam)

instance fixedSetUnderloadFamily_decidable {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (η lam : ℝ) (B : Finset (Fin n)) :
    DecidablePred (fixedSetUnderloadFamily available recording η lam B) :=
  fixedUnderloadEvent_decidable _ _ _

/-- Step 3 before the entropy simplification: unioning the fixed-set lower
deviation bound over exactly `n.choose b` candidate sets. -/
theorem fixedCard_underload_union_bound {n b : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    {η lam : ℝ} (hη : 0 ≤ η) (hlam : 0 ≤ lam) (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (candidateSets n b)
          (fixedSetUnderloadFamily available recording η lam)) depth [] ≤
      (n.choose b : ℝ) *
        Real.exp (-(AdaptiveBernoulli.lowerRate * η) * (b : ℝ) * lam) := by
  have hvalid := uniformChoiceWeight_valid available hnonempty
  have hfixed : ∀ B ∈ candidateSets n b,
      hitProbability (uniformChoiceWeight available)
          (fixedSetUnderloadFamily available recording η lam B) depth [] ≤
        Real.exp (-(AdaptiveBernoulli.lowerRate * η) * (b : ℝ) * lam) := by
    intro B hB
    have hcard : B.card = b := (Finset.mem_powersetCard.mp hB).2
    simpa [fixedSetUnderloadFamily, hcard] using
      (stoppedChoice_fixed_set_exponent available hnonempty B (recording B)
        hη hlam depth)
  have hunion := hitProbability_finiteUnion_le_card_mul hvalid
    (candidateSets n b)
    (fixedSetUnderloadFamily available recording η lam) depth []
    (Real.exp (-(AdaptiveBernoulli.lowerRate * η) * (b : ℝ) * lam))
    hfixed
  simpa [candidateSets, Finset.card_powersetCard] using hunion

/-! ## Entropy cost of choosing `B` -/

/-- Every nonnegative term of the exponential series is bounded by its sum. -/
lemma pow_div_factorial_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
  have hs := NormedSpace.expSeries_div_summable ℝ x
  have hterm := hs.sum_le_tsum ({k} : Finset ℕ) (by
    intro i hi
    exact div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg i.factorial))
  simp only [Finset.sum_singleton] at hterm
  rw [(NormedSpace.expSeries_div_hasSum_exp ℝ x).tsum_eq] at hterm
  simpa only [Real.exp_eq_exp_ℝ] using hterm

/-- Elementary factorial lower bound `b^b ≤ e^b b!`, obtained from the
`b`-th term of the exponential series. -/
lemma self_pow_le_exp_one_pow_mul_factorial (b : ℕ) :
    (b : ℝ) ^ b ≤ Real.exp 1 ^ b * (b.factorial : ℝ) := by
  have hterm := pow_div_factorial_le_exp (b : ℝ) (Nat.cast_nonneg b) b
  have hfac : (0 : ℝ) < b.factorial := by positivity
  rw [div_le_iff₀ hfac] at hterm
  rw [← Real.exp_nat_mul] 
  simpa using hterm

/-- The standard entropy estimate `n.choose b ≤ (e n / b)^b`. -/
theorem choose_le_exp_mul_div_pow (n b : ℕ) (hb : 0 < b) :
    (n.choose b : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ b := by
  have hchoose : (n.choose b : ℝ) ≤ (n : ℝ) ^ b / (b.factorial : ℝ) :=
    Nat.choose_le_pow_div b n
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbpow : (0 : ℝ) < (b : ℝ) ^ b := pow_pos hbR b
  have hfac : (0 : ℝ) < b.factorial := by positivity
  have hfactorial := self_pow_le_exp_one_pow_mul_factorial b
  have hinv : 1 / (b.factorial : ℝ) ≤
      Real.exp 1 ^ b / (b : ℝ) ^ b := by
    rw [div_le_div_iff₀ hfac hbpow]
    simpa [mul_comm] using hfactorial
  calc
    (n.choose b : ℝ) ≤ (n : ℝ) ^ b / (b.factorial : ℝ) := hchoose
    _ = (n : ℝ) ^ b * (1 / (b.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ b * (Real.exp 1 ^ b / (b : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (Nat.cast_nonneg n) b)
    _ = (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ b := by
      simp only [mul_pow, div_pow]
      ring

/-- The ceiling choice from the paper, parameterized by `λ = n/s`. -/
def candidateSize (n : ℕ) (α lam : ℝ) : ℕ :=
  ⌈(n : ℝ) * Real.exp (-α * lam)⌉₊

lemma candidateSize_lower (n : ℕ) (α lam : ℝ) :
    (n : ℝ) * Real.exp (-α * lam) ≤ (candidateSize n α lam : ℝ) := by
  exact Nat.le_ceil _

lemma candidateSize_pos {n : ℕ} (hn : 0 < n) (α lam : ℝ) :
    0 < candidateSize n α lam := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by exact_mod_cast hn) (Real.exp_pos _)

/-- The ceiling lower bound implies the logarithmic estimate used to pay for
the `n.choose b` candidate sets. -/
lemma log_exp_mul_card_div_candidate_le {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b) {α lam : ℝ}
    (hbLower : (n : ℝ) * Real.exp (-α * lam) ≤ (b : ℝ)) :
    Real.log (Real.exp 1 * (n : ℝ) / (b : ℝ)) ≤ 1 + α * lam := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hexp : 0 < Real.exp (α * lam) := Real.exp_pos _
  have hcancel : Real.exp (-α * lam) * Real.exp (α * lam) = 1 := by
    rw [← Real.exp_add]
    simp
  have hratio : (n : ℝ) / (b : ℝ) ≤ Real.exp (α * lam) := by
    rw [div_le_iff₀ hbR]
    calc
      (n : ℝ) = ((n : ℝ) * Real.exp (-α * lam)) *
          Real.exp (α * lam) := by rw [mul_assoc, hcancel, mul_one]
      _ ≤ (b : ℝ) * Real.exp (α * lam) :=
        mul_le_mul_of_nonneg_right hbLower hexp.le
      _ = Real.exp (α * lam) * (b : ℝ) := by ring
  have hbasePos : 0 < Real.exp 1 * (n : ℝ) / (b : ℝ) := by positivity
  have hbase : Real.exp 1 * (n : ℝ) / (b : ℝ) ≤
      Real.exp (1 + α * lam) := by
    rw [Real.exp_add]
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le)
  calc
    Real.log (Real.exp 1 * (n : ℝ) / (b : ℝ)) ≤
        Real.log (Real.exp (1 + α * lam)) :=
      Real.log_le_log hbasePos hbase
    _ = 1 + α * lam := Real.log_exp _

/-- Once the logarithmic number of candidate sets uses at most half of the
Chernoff exponent, the union retains the other half. -/
theorem choose_mul_exp_le_half_exponent {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b) {β lam : ℝ}
    (hbudget : Real.log (Real.exp 1 * (n : ℝ) / (b : ℝ)) ≤
      (β / 2) * lam) :
    (n.choose b : ℝ) * Real.exp (-β * (b : ℝ) * lam) ≤
      Real.exp (-(β / 2) * (b : ℝ) * lam) := by
  let base : ℝ := Real.exp 1 * (n : ℝ) / (b : ℝ)
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  have hchoose := choose_le_exp_mul_div_pow n b hb
  have hpow : base ^ b = Real.exp ((b : ℝ) * Real.log base) := by
    rw [Real.exp_nat_mul, Real.exp_log hbase]
  have hexponent : (b : ℝ) * Real.log base - β * (b : ℝ) * lam ≤
      -(β / 2) * (b : ℝ) * lam := by
    have hbnonneg : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    change Real.log base ≤ (β / 2) * lam at hbudget
    nlinarith
  calc
    (n.choose b : ℝ) * Real.exp (-β * (b : ℝ) * lam) ≤
        base ^ b * Real.exp (-β * (b : ℝ) * lam) :=
      mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
    _ = Real.exp ((b : ℝ) * Real.log base - β * (b : ℝ) * lam) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(β / 2) * (b : ℝ) * lam) :=
      Real.exp_le_exp.mpr hexponent

/-- Step 3's complete entropy simplification from the paper's two displayed
inequalities. -/
theorem candidate_union_exponent {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b) {α β lam : ℝ}
    (hbLower : (n : ℝ) * Real.exp (-α * lam) ≤ (b : ℝ))
    (hLambda : 1 + α * lam ≤ (β / 2) * lam) :
    (n.choose b : ℝ) * Real.exp (-β * (b : ℝ) * lam) ≤
      Real.exp (-(β / 2) * (b : ℝ) * lam) := by
  apply choose_mul_exp_le_half_exponent hn hb
  exact (log_exp_mul_card_div_candidate_le hn hb hbLower).trans hLambda

/-- The fixed-cardinality stopped event after paying the full combinatorial
cost.  This is the probabilistic conclusion of Steps 2 and 3. -/
theorem fixedCard_underload_exponential_bound {n b : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (hn : 0 < n) (hb : 0 < b)
    {η α β lam : ℝ} (hη : 0 ≤ η) (hlam : 0 ≤ lam)
    (hβ : β = AdaptiveBernoulli.lowerRate * η)
    (hbLower : (n : ℝ) * Real.exp (-α * lam) ≤ (b : ℝ))
    (hLambda : 1 + α * lam ≤ (β / 2) * lam)
    (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (candidateSets n b)
          (fixedSetUnderloadFamily available recording η lam)) depth [] ≤
      Real.exp (-(β / 2) * (b : ℝ) * lam) := by
  calc
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (candidateSets n b)
          (fixedSetUnderloadFamily available recording η lam)) depth [] ≤
        (n.choose b : ℝ) * Real.exp (-β * (b : ℝ) * lam) := by
      simpa [hβ] using
        (fixedCard_underload_union_bound available hnonempty recording hη hlam depth)
    _ ≤ Real.exp (-(β / 2) * (b : ℝ) * lam) :=
      candidate_union_exponent hn hb hbLower hLambda

/-- Turning the remaining exponential into the `n⁻⁴` bound used before the
last union over `s`. -/
lemma exp_half_exponent_le_inv_fourth {n : ℕ} (hn : 0 < n)
    {β b lam : ℝ}
    (hlarge : 4 * Real.log (n : ℝ) ≤ (β / 2) * b * lam) :
    Real.exp (-(β / 2) * b * lam) ≤ 1 / (n : ℝ) ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    Real.exp (-(β / 2) * b * lam) ≤
        Real.exp (-4 * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1 / (n : ℝ) ^ 4 := by
      rw [show -4 * Real.log (n : ℝ) =
          -((4 : ℝ) * Real.log (n : ℝ)) by ring,
        Real.exp_neg]
      have hexpFour : Real.exp ((4 : ℝ) * Real.log (n : ℝ)) =
          (n : ℝ) ^ 4 := by
        simpa [Real.exp_log hnR] using
          (Real.exp_nat_mul (Real.log (n : ℝ)) 4)
      rw [hexpFour]
      simp [one_div]

/-- At most `n` possible positive active-set sizes each costing `n⁻⁴`
produce the paper's `n⁻³` failure probability. -/
theorem union_over_active_cardinalities {α : Type*} [Fintype α]
    {weight : History α → α → ℝ} (hweight : ValidLaw weight)
    (n : ℕ) (hn : 0 < n) (event : ℕ → History α → Prop)
    [∀ s, DecidablePred (event s)] (depth : ℕ) (history : History α)
    (hfixed : ∀ s ∈ Finset.Icc 1 n,
      hitProbability weight (event s) depth history ≤ 1 / (n : ℝ) ^ 4) :
    hitProbability weight (finiteUnionEvent (Finset.Icc 1 n) event)
        depth history ≤ 1 / (n : ℝ) ^ 3 := by
  have hunion := hitProbability_finiteUnion_le_card_mul hweight
    (Finset.Icc 1 n) event depth history (1 / (n : ℝ) ^ 4) hfixed
  have hcard : (Finset.Icc 1 n).card = n := by
    simp [hn]
  rw [hcard] at hunion
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    hitProbability weight (finiteUnionEvent (Finset.Icc 1 n) event)
        depth history ≤ (n : ℝ) * (1 / (n : ℝ) ^ 4) := hunion
    _ = 1 / (n : ℝ) ^ 3 := by
      field_simp
      ring

/-! ## One explicit absolute choice of constants -/

/-- A convenient concrete choice; the paper notes that `1/10` also works. -/
def etaZero : ℝ := 1 / 16

def betaZero : ℝ := AdaptiveBernoulli.lowerRate * etaZero

def alphaZero : ℝ := betaZero / 8

lemma etaZero_pos : 0 < etaZero := by norm_num [etaZero]

lemma etaZero_lt_one : etaZero < 1 := by norm_num [etaZero]

lemma betaZero_pos : 0 < betaZero := by
  exact mul_pos AdaptiveBernoulli.lowerRate_pos etaZero_pos

lemma alphaZero_pos : 0 < alphaZero := by
  exact div_pos betaZero_pos (by norm_num)

lemma betaZero_eq_eight_mul_alphaZero : betaZero = 8 * alphaZero := by
  unfold alphaZero
  ring

/-- Verification of the paper's required strict inequality
`I(η₀) > log 2`. -/
theorem rateFunction_etaZero_gt_log_two :
    Real.log 2 < rateFunction etaZero := by
  have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hinv] at h
    linarith
  have hlogSixteen : Real.log 16 = 4 * Real.log 2 := by
    calc
      Real.log 16 = Real.log ((2 : ℝ) ^ 4) := by norm_num
      _ = (4 : ℝ) * Real.log 2 := Real.log_pow 2 4
  unfold rateFunction etaZero
  rw [show (1 : ℝ) / (1 / 16) = 16 by norm_num, hlogSixteen]
  linarith

/-- Existence of the absolute `λ₀` required in Step 3.  The second inequality
is the only asymptotic ingredient: `λ exp (-α λ) → 0`. -/
theorem exists_lambdaThreshold {α β : ℝ} (hα : 0 < α)
    (hβα : β = 8 * α) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧
      ∀ lam : ℝ, lambda0 ≤ lam →
        1 / α ≤ lam ∧
        1 + α * lam ≤ (β / 2) * lam ∧
        2 * lam * Real.exp (-α * lam) ≤ 1 / 4 := by
  have htend : Tendsto (fun x : ℝ => x * Real.exp (-α * x))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 α hα)
  have hevent : ∀ᶠ x : ℝ in atTop,
      x * Real.exp (-α * x) < 1 / 8 :=
    htend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨L, hL⟩ := eventually_atTop.1 hevent
  let lambda0 : ℝ :=
    max 1 (max (1 / α) (max (1 / (3 * α)) L))
  have hlambda0 : 0 < lambda0 := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨lambda0, hlambda0, ?_⟩
  intro lam hlam
  have hInv : 1 / α ≤ lam := by
    exact ((le_max_left (1 / α) (max (1 / (3 * α)) L)).trans
      (le_max_right 1 (max (1 / α) (max (1 / (3 * α)) L)))).trans hlam
  have hThird : 1 / (3 * α) ≤ lam := by
    exact (((le_max_left (1 / (3 * α)) L).trans
      (le_max_right (1 / α) (max (1 / (3 * α)) L))).trans
      (le_max_right 1 (max (1 / α) (max (1 / (3 * α)) L)))).trans hlam
  have hLamL : L ≤ lam := by
    exact (((le_max_right (1 / (3 * α)) L).trans
      (le_max_right (1 / α) (max (1 / (3 * α)) L))).trans
      (le_max_right 1 (max (1 / α) (max (1 / (3 * α)) L)))).trans hlam
  have hthreeAlpha : 0 < 3 * α := mul_pos (by norm_num) hα
  have hone : 1 ≤ lam * (3 * α) := by
    exact (div_le_iff₀ hthreeAlpha).mp hThird
  have hlinear : 1 + α * lam ≤ (β / 2) * lam := by
    rw [hβα]
    nlinarith
  have hsmall := hL lam hLamL
  have hdecay : 2 * lam * Real.exp (-α * lam) ≤ 1 / 4 := by
    nlinarith
  exact ⟨hInv, hlinear, hdecay⟩

theorem exists_absolute_lambdaZero :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧
      ∀ lam : ℝ, lambda0 ≤ lam →
        1 / alphaZero ≤ lam ∧
        1 + alphaZero * lam ≤ (betaZero / 2) * lam ∧
        2 * lam * Real.exp (-alphaZero * lam) ≤ 1 / 4 :=
  exists_lambdaThreshold alphaZero_pos betaZero_eq_eight_mul_alphaZero

/-! ## The lower bound on `b λ` -/

/-- On `[1, X]`, the function `y ↦ y exp (-y)` is bounded below by its
value at `X`.  This elementary logarithmic proof avoids a calculus detour. -/
lemma mul_exp_neg_anti_on_one {X y : ℝ} (hy : 1 ≤ y) (hyX : y ≤ X) :
    X * Real.exp (-X) ≤ y * Real.exp (-y) := by
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hXpos : 0 < X := hypos.trans_le hyX
  have hratioPos : 0 < X / y := div_pos hXpos hypos
  have hquotient : X / y - 1 ≤ X - y := by
    rw [show X / y - 1 = (X - y) / y by
      field_simp [hypos.ne']]
    apply (div_le_iff₀ hypos).mpr
    have hprod : 0 ≤ (y - 1) * (X - y) :=
      mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hyX)
    nlinarith
  have hlog : Real.log (X / y) ≤ X - y :=
    (Real.log_le_sub_one_of_pos hratioPos).trans hquotient
  have hratioExp : X / y ≤ Real.exp (X - y) := by
    calc
      X / y = Real.exp (Real.log (X / y)) :=
        (Real.exp_log hratioPos).symm
      _ ≤ Real.exp (X - y) := Real.exp_le_exp.mpr hlog
  have hmul := mul_le_mul_of_nonneg_right hratioExp
    (mul_nonneg hypos.le (Real.exp_pos (-X)).le)
  calc
    X * Real.exp (-X) = (X / y) * (y * Real.exp (-X)) := by
      field_simp [hypos.ne']
      ring
    _ ≤ Real.exp (X - y) * (y * Real.exp (-X)) := hmul
    _ = y * Real.exp (-y) := by
      rw [show Real.exp (X - y) * (y * Real.exp (-X)) =
          y * (Real.exp (X - y) * Real.exp (-X)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- The paper's case split proving `b λ ≥ (log n)/α` for
`b = ceil (n exp (-α λ))`, once `log n ≥ 1` and `λ ≥ 1/α`. -/
theorem candidateSize_mul_lambda_ge_log_div {n : ℕ}
    (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    {α lam : ℝ} (hα : 0 < α) (hLam : 1 / α ≤ lam) :
    Real.log (n : ℝ) / α ≤ (candidateSize n α lam : ℝ) * lam := by
  let N : ℝ := n
  let X : ℝ := Real.log N
  let y : ℝ := α * lam
  let base : ℝ := N * Real.exp (-y)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hXone : 1 ≤ X := by simpa [X, N] using hlogn
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hlamPos : 0 < lam :=
    (div_pos one_pos hα).trans_le hLam
  have hyOne : 1 ≤ y := by
    have hone : 1 ≤ lam * α := (div_le_iff₀ hα).mp hLam
    simpa [y, mul_comm] using hone
  have hyPos : 0 < y := zero_lt_one.trans_le hyOne
  have hcancel : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp
  have hbasePos : 0 < base := mul_pos hN (Real.exp_pos _)
  have hceilLower : base ≤ (candidateSize n α lam : ℝ) := by
    simpa [base, y, N] using candidateSize_lower n α lam
  by_cases hbaseSmall : base < 1
  · have hNexp : N < Real.exp y := by
      calc
        N = base * Real.exp y := by
          dsimp [base]
          rw [mul_assoc, hcancel, mul_one]
        _ < 1 * Real.exp y :=
          mul_lt_mul_of_pos_right hbaseSmall (Real.exp_pos y)
        _ = Real.exp y := one_mul _
    have hXy : X < y := by
      apply (Real.exp_lt_exp).mp
      simpa [X, Real.exp_log hN] using hNexp
    have hDiv : X / α < lam := by
      apply (div_lt_iff₀ hα).mpr
      simpa [y, mul_comm] using hXy
    have hbOne : (1 : ℝ) ≤ candidateSize n α lam := by
      exact_mod_cast (candidateSize_pos hn α lam)
    have hlamLe : lam ≤ (candidateSize n α lam : ℝ) * lam := by
      nlinarith
    simpa [X, N] using hDiv.le.trans hlamLe
  · have hbaseOne : 1 ≤ base := le_of_not_gt hbaseSmall
    have hExpYN : Real.exp y ≤ N := by
      have hmul := mul_le_mul_of_nonneg_right hbaseOne (Real.exp_pos y).le
      calc
        Real.exp y = 1 * Real.exp y := by ring
        _ ≤ base * Real.exp y := hmul
        _ = N := by
          dsimp [base]
          rw [mul_assoc, hcancel, mul_one]
    have hyX : y ≤ X := by
      apply (Real.exp_le_exp).mp
      simpa [X, Real.exp_log hN] using hExpYN
    have hdecrease : X * Real.exp (-X) ≤ y * Real.exp (-y) :=
      mul_exp_neg_anti_on_one hyOne hyX
    have hExpNegX : Real.exp (-X) = 1 / N := by
      rw [Real.exp_neg]
      simp [X, Real.exp_log hN, one_div]
    have hscaled := mul_le_mul_of_nonneg_left hdecrease
      (div_nonneg hN.le hα.le)
    have hleft : (N / α) * (X * Real.exp (-X)) = X / α := by
      rw [hExpNegX]
      field_simp
      ring
    have hright : (N / α) * (y * Real.exp (-y)) =
        base * lam := by
      dsimp [base, y]
      field_simp
      ring
    rw [hleft, hright] at hscaled
    have hceilMul := mul_le_mul_of_nonneg_right hceilLower hlamPos.le
    simpa [X, N] using hscaled.trans hceilMul

/-- For the paper's relation `β = 8α`, the preceding lower bound is exactly
what is needed to retain four logarithms in the final exponent. -/
lemma candidate_half_exponent_ge_four_log {n : ℕ}
    (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    {α β lam : ℝ} (hα : 0 < α) (hβα : β = 8 * α)
    (hLam : 1 / α ≤ lam) :
    4 * Real.log (n : ℝ) ≤
      (β / 2) * (candidateSize n α lam : ℝ) * lam := by
  have hproduct := candidateSize_mul_lambda_ge_log_div hn hlogn hα hLam
  have hαnonneg := hα.le
  rw [hβα]
  have hscaled := mul_le_mul_of_nonneg_left hproduct
    (by positivity : 0 ≤ 4 * α)
  have hαne := hα.ne'
  calc
    4 * Real.log (n : ℝ) =
        (4 * α) * (Real.log (n : ℝ) / α) := by
      field_simp
      ring
    _ ≤ (4 * α) * ((candidateSize n α lam : ℝ) * lam) := hscaled
    _ = (8 * α / 2) * (candidateSize n α lam : ℝ) * lam := by ring

/-- One active-cardinality value has failure probability at most `n⁻⁴`, with
the exact ceiling choice and the concrete stopped-choice process. -/
theorem candidateSize_underload_le_inv_fourth {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : Finset (Fin n) → History (Fin n) → Bool)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hLamInv : 1 / alphaZero ≤ lam)
    (hLambda : 1 + alphaZero * lam ≤ (betaZero / 2) * lam)
    (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (candidateSets n (candidateSize n alphaZero lam))
          (fixedSetUnderloadFamily available recording etaZero lam)) depth [] ≤
      1 / (n : ℝ) ^ 4 := by
  let b := candidateSize n alphaZero lam
  have hb : 0 < b := candidateSize_pos hn alphaZero lam
  have hExp := fixedCard_underload_exponential_bound available hnonempty
    recording hn hb etaZero_pos.le hlam (show betaZero =
      AdaptiveBernoulli.lowerRate * etaZero by rfl)
    (candidateSize_lower n alphaZero lam) hLambda depth
  have hlarge : 4 * Real.log (n : ℝ) ≤
      (betaZero / 2) * (b : ℝ) * lam :=
    candidate_half_exponent_ge_four_log hn hlogn alphaZero_pos
      betaZero_eq_eight_mul_alphaZero hLamInv
  exact hExp.trans (exp_half_exponent_le_inv_fourth hn hlarge)

def activeCardinalityUnderloadEvent {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : ℕ → Finset (Fin n) → History (Fin n) → Bool)
    (lam : ℕ → ℝ) (s : ℕ) : History (Fin n) → Prop :=
  finiteUnionEvent (candidateSets n (candidateSize n alphaZero (lam s)))
    (fixedSetUnderloadFamily available (recording s) etaZero (lam s))

instance activeCardinalityUnderloadEvent_decidable {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (recording : ℕ → Finset (Fin n) → History (Fin n) → Bool)
    (lam : ℕ → ℝ) (s : ℕ) :
    DecidablePred (activeCardinalityUnderloadEvent available recording lam s) :=
  finiteUnionEvent_decidable _ _

/-- The complete Step 3 union over every positive active-set cardinality. -/
theorem candidateSize_underload_all_cardinalities {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (recording : ℕ → Finset (Fin n) → History (Fin n) → Bool)
    (lam : ℕ → ℝ) (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hlam : ∀ s ∈ Finset.Icc 1 n, 0 ≤ lam s)
    (hLamInv : ∀ s ∈ Finset.Icc 1 n, 1 / alphaZero ≤ lam s)
    (hLambda : ∀ s ∈ Finset.Icc 1 n,
      1 + alphaZero * lam s ≤ (betaZero / 2) * lam s)
    (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (finiteUnionEvent (Finset.Icc 1 n)
          (activeCardinalityUnderloadEvent available recording lam)) depth [] ≤
      1 / (n : ℝ) ^ 3 := by
  apply union_over_active_cardinalities
    (uniformChoiceWeight_valid available hnonempty) n hn _ depth []
  intro s hs
  exact candidateSize_underload_le_inv_fourth available hnonempty
    (recording s) hn hlogn (hlam s hs) (hLamInv s hs) (hLambda s hs) depth

/-- Steps 1--3 together on the same full labelled filtration.  The two bad
events cost an exponentially small term and `n⁻³`, respectively. -/
theorem load_bound_tree_failure {n : ℕ}
    (available : History (Fin n) → Finset (Fin n))
    (hnonempty : ∀ history, (available history).Nonempty)
    (potentialRecording : Finset (Fin n) → History (Fin n) → Bool)
    (underloadRecording : ℕ → Finset (Fin n) → History (Fin n) → Bool)
    (lam : ℕ → ℝ) (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hlam : ∀ s ∈ Finset.Icc 1 n, 0 ≤ lam s)
    (hLamInv : ∀ s ∈ Finset.Icc 1 n, 1 / alphaZero ≤ lam s)
    (hLambda : ∀ s ∈ Finset.Icc 1 n,
      1 + alphaZero * lam s ≤ (betaZero / 2) * lam s)
    (depth : ℕ) :
    hitProbability (uniformChoiceWeight available)
        (fun h =>
          finiteUnionEvent Finset.univ.powerset
              (potentialFailureEvent available potentialRecording etaZero) h ∨
            finiteUnionEvent (Finset.Icc 1 n)
              (activeCardinalityUnderloadEvent available
                underloadRecording lam) h)
        depth [] ≤
      Real.exp (-(rateFunction etaZero - Real.log 2) * (n : ℝ)) +
        1 / (n : ℝ) ^ 3 := by
  have hOr := hitProbability_or_le
    (uniformChoiceWeight_valid available hnonempty)
    (finiteUnionEvent Finset.univ.powerset
      (potentialFailureEvent available potentialRecording etaZero))
    (finiteUnionEvent (Finset.Icc 1 n)
      (activeCardinalityUnderloadEvent available underloadRecording lam))
    depth []
  exact hOr.trans (add_le_add
    (allSet_potential_exponential_bound available hnonempty potentialRecording
      etaZero_pos etaZero_lt_one hn depth)
    (candidateSize_underload_all_cardinalities available hnonempty
      underloadRecording lam hn hlogn hlam hLamInv hLambda depth))

/-! ## From individual underload to demand on every large set -/

def underloadedGoods {γ : Type*} [DecidableEq γ]
    (active : Finset γ) (load : γ → ℕ) (q : ℝ) : Finset γ :=
  active.filter (fun g => (load g : ℝ) < q)

def wellLoadedIn {γ : Type*} [DecidableEq γ]
    (T : Finset γ) (load : γ → ℕ) (q : ℝ) : Finset γ :=
  T.filter (fun g => q ≤ (load g : ℝ))

def setLoad {γ : Type*} [DecidableEq γ]
    (load : γ → ℕ) (T : Finset γ) : ℝ :=
  ∑ g ∈ T, (load g : ℝ)

/-- If no `b`-set consists entirely of underloaded active goods, then fewer
than `b` active goods are underloaded, and conversely. -/
theorem no_bad_candidate_iff_few_underloaded {γ : Type*} [DecidableEq γ]
    (ambient active : Finset γ) (hactive : active ⊆ ambient)
    (load : γ → ℕ) (q : ℝ) (b : ℕ) :
    (¬ ∃ B ∈ ambient.powersetCard b,
        B ⊆ underloadedGoods active load q) ↔
      (underloadedGoods active load q).card < b := by
  constructor
  · intro hnone
    by_contra hnot
    have hbcard : b ≤ (underloadedGoods active load q).card :=
      Nat.le_of_not_gt hnot
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hbcard
    apply hnone
    refine ⟨B, ?_, hBsub⟩
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hBcard⟩
    have hunder : underloadedGoods active load q ⊆ active := by
      intro g hg
      exact (Finset.mem_filter.mp hg).1
    exact hBsub.trans (hunder.trans hactive)
  · intro hfew ⟨B, hBmem, hBsub⟩
    have hBcard : B.card = b := (Finset.mem_powersetCard.mp hBmem).2
    have hcardLe := Finset.card_le_card hBsub
    omega

/-- Step 4: if fewer than `b` active goods have load below `q`, every active
set of at least `2b` goods has total load at least `q |T| / 2`. -/
theorem demand_of_few_underloaded {γ : Type*} [DecidableEq γ]
    (active : Finset γ) (load : γ → ℕ) {q : ℝ} (hq : 0 ≤ q)
    {b : ℕ}
    (hfew : (underloadedGoods active load q).card < b)
    (T : Finset γ) (hTactive : T ⊆ active)
    (hTlarge : 2 * b ≤ T.card) :
    q * (T.card : ℝ) / 2 ≤ setLoad load T := by
  let bad : Finset γ := T.filter (fun g => (load g : ℝ) < q)
  let good : Finset γ := wellLoadedIn T load q
  have hbadSub : bad ⊆ underloadedGoods active load q := by
    intro g hg
    have hmem := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨hTactive hmem.1, hmem.2⟩
  have hbadLt : bad.card < b :=
    (Finset.card_le_card hbadSub).trans_lt hfew
  have hdisjoint : Disjoint bad good := by
    rw [Finset.disjoint_left]
    intro g hgbad hggood
    have hlt := (Finset.mem_filter.mp hgbad).2
    have hge := (Finset.mem_filter.mp hggood).2
    exact (not_lt_of_ge hge) hlt
  have hunion : bad ∪ good = T := by
    ext g
    simp only [bad, good, wellLoadedIn, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · rintro (⟨hgT, hlt⟩ | ⟨hgT, hge⟩) <;> exact hgT
    · intro hgT
      exact (lt_or_ge (load g : ℝ) q).imp (And.intro hgT) (And.intro hgT)
  have hcardEq : T.card = bad.card + good.card := by
    rw [← hunion]
    exact Finset.card_union_of_disjoint hdisjoint
  have hhalf : T.card ≤ 2 * good.card := by omega
  have hgoodSubset : good ⊆ T := Finset.filter_subset _ _
  have hgoodSum : q * (good.card : ℝ) ≤
      ∑ g ∈ good, (load g : ℝ) := by
    calc
      q * (good.card : ℝ) = ∑ _g ∈ good, q := by simp [mul_comm]
      _ ≤ ∑ g ∈ good, (load g : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        exact (Finset.mem_filter.mp hg).2
  have hsumSubset : (∑ g ∈ good, (load g : ℝ)) ≤ setLoad load T := by
    unfold setLoad
    exact Finset.sum_le_sum_of_subset_of_nonneg hgoodSubset
      (fun g hgT hgNot => Nat.cast_nonneg (load g))
  have hhalfR : (T.card : ℝ) ≤ 2 * (good.card : ℝ) := by
    exact_mod_cast hhalf
  calc
    q * (T.card : ℝ) / 2 ≤ q * (good.card : ℝ) := by nlinarith
    _ ≤ ∑ g ∈ good, (load g : ℝ) := hgoodSum
    _ ≤ setLoad load T := hsumSubset

/-- The displayed demand bound with `q = (η/4)(n/s)`. -/
theorem paper_demand_bound {γ : Type*} [DecidableEq γ]
    (active : Finset γ) (load : γ → ℕ)
    {η n s : ℝ} (hη : 0 ≤ η) (hn : 0 ≤ n) (hs : 0 < s)
    {b : ℕ}
    (hfew : (underloadedGoods active load ((η / 4) * (n / s))).card < b)
    (T : Finset γ) (hTactive : T ⊆ active)
    (hTlarge : 2 * b ≤ T.card) :
    (η / 8) * (n * (T.card : ℝ) / s) ≤ setLoad load T := by
  have hq : 0 ≤ (η / 4) * (n / s) := by positivity
  have hbound := demand_of_few_underloaded active load hq hfew T
    hTactive hTlarge
  convert hbound using 1
  field_simp
  ring

end ProbabilisticSerial.LoadBound
