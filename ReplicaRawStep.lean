import ReplicaLaw
import UniformSubsetRank
import Mathlib.Tactic

/-!
# One raw-label step coupled to the actual replica profile

The accepted type is already conditionally uniform on the available types.
The kernel below augments a fresh query with rejected labels. Its profile
marginal is unchanged, its raw label is uniform on all types, and a rejected
label leaves the conditional profile law unchanged. This is one step of the
coupling, not yet a construction of the complete raw-label process.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawStep
open UniformProduct UniformPermutation ReplicaPS ReplicaChoiceMachine

variable {m q : ℕ} [Nonempty (Fin (m * q))]

def fiber (reference : ReplicaPS.Profile m q) (depth : ℕ) :=
  ReplicaChoiceMachine.pathFiber depth (history reference depth)

def available (reference : ReplicaPS.Profile m q) (depth : ℕ) :=
  queryTypes (history reference depth)

def chosenType (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (profile : ReplicaPS.Profile m q) : Fin m :=
  typeOf (answer profile (history reference depth))

def rawWeight (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (profile : ReplicaPS.Profile m q) (g : Fin m) : ℝ :=
  ((available reference depth).card : ℝ) / m *
      (if chosenType reference depth profile = g then 1 else 0) +
    (if g ∈ available reference depth then 0 else 1 / (m : ℝ))

lemma rawWeight_nonneg (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (profile : ReplicaPS.Profile m q) (g : Fin m) :
    0 ≤ rawWeight reference depth profile g := by
  unfold rawWeight
  positivity

theorem rawWeight_sum (hm : 0 < m) (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (profile : ReplicaPS.Profile m q) :
    (∑ g : Fin m, rawWeight reference depth profile g) = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq (g : Fin m) :
      (if g ∈ available reference depth then (0 : ℝ) else 1 / (m : ℝ)) =
        (1 - if g ∈ available reference depth then (1 : ℝ) else 0) / m := by
    split_ifs <;> simp
  unfold rawWeight
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp
  field_simp

lemma chosenType_mem (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (profile : ReplicaPS.Profile m q) (hp : profile ∈ fiber reference depth) :
    chosenType reference depth profile ∈ available reference depth := by
  have hh : history profile depth = history reference depth := (Finset.mem_filter.mp hp).2
  have hA : (queryTypes (history profile depth)).Nonempty := by
    rw [hh]
    exact stochastic_nonempty _ hs
  unfold chosenType available
  rw [← hh, answer_type profile depth hA]
  exact PSProcess.favorite_mem _ _ _

theorem rawWeight_rejected (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (profile : ReplicaPS.Profile m q) (hp : profile ∈ fiber reference depth)
    (g : Fin m) (hg : g ∉ available reference depth) :
    rawWeight reference depth profile g = 1 / (m : ℝ) := by
  have hne : chosenType reference depth profile ≠ g := by
    intro heq
    exact hg (heq ▸ chosenType_mem reference depth hs profile hp)
  simp [rawWeight, hne, hg]

theorem raw_label_uniform (hm : 0 < m) (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true) (g : Fin m) :
    (𝔼 profile ∈ fiber reference depth, rawWeight reference depth profile g) =
      1 / (m : ℝ) := by
  have hC := ReplicaChoiceMachine.pathFiber_nonempty reference depth
  by_cases hg : g ∈ available reference depth
  · have hA : ((available reference depth).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (stochastic_nonempty _ hs)).ne'
    unfold rawWeight
    simp only [hg, if_true, add_zero]
    rw [← Finset.mul_expect]
    have hp := fresh_answer_probability reference depth hs g hg
    change (𝔼 profile ∈ fiber reference depth,
      if chosenType reference depth profile = g then (1 : ℝ) else 0) =
      1 / ((available reference depth).card : ℝ) at hp
    rw [hp]
    field_simp
    <;> ring
  · calc
      _ = 𝔼 _profile ∈ fiber reference depth, 1 / (m : ℝ) := by
        apply Finset.expect_congr rfl
        intro profile hp
        exact rawWeight_rejected reference depth hs profile hp g hg
      _ = _ := Finset.expect_const hC _

/-- Summing over the auxiliary raw label preserves every profile statistic. -/
theorem profile_marginal (hm : 0 < m) (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (F : ReplicaPS.Profile m q → ℝ) :
    (𝔼 profile ∈ fiber reference depth, ∑ g : Fin m,
      rawWeight reference depth profile g * F profile) =
      𝔼 profile ∈ fiber reference depth, F profile := by
  apply Finset.expect_congr rfl
  intro profile hp
  rw [← Finset.sum_mul, rawWeight_sum hm, one_mul]

theorem rejected_weighted_expectation (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (g : Fin m) (hg : g ∉ available reference depth)
    (F : ReplicaPS.Profile m q → ℝ) :
    (𝔼 profile ∈ fiber reference depth, rawWeight reference depth profile g * F profile) =
      (1 / (m : ℝ)) * (𝔼 profile ∈ fiber reference depth, F profile) := by
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro profile hp
  rw [rawWeight_rejected reference depth hs profile hp g hg]

def acceptedFiber (reference : ReplicaPS.Profile m q) (depth : ℕ) (g : Fin m) :=
  (fiber reference depth).filter (fun profile => chosenType reference depth profile = g)

lemma acceptedFiber_card_ratio (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (g : Fin m) (hg : g ∈ available reference depth) :
    ((acceptedFiber reference depth g).card : ℝ) / (fiber reference depth).card =
      1 / ((available reference depth).card : ℝ) := by
  have h := fresh_answer_probability reference depth hs g hg
  change probability (fiber reference depth)
    (fun profile => chosenType reference depth profile = g) = _ at h
  rw [UniformSubsetRank.probability_eq_card_filter_div] at h
  exact h

lemma acceptedFiber_nonempty (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (g : Fin m) (hg : g ∈ available reference depth) :
    (acceptedFiber reference depth g).Nonempty := by
  have h := acceptedFiber_card_ratio reference depth hs g hg
  have hA : (0 : ℝ) < (available reference depth).card := by
    exact_mod_cast Finset.card_pos.mpr (stochastic_nonempty _ hs)
  by_contra hn
  have hz : (acceptedFiber reference depth g).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  rw [hz, Nat.cast_zero, zero_div] at h
  have hp : (0 : ℝ) < 1 / (available reference depth).card := by positivity
  linarith

lemma expect_indicator_mul {α : Type*} (C : Finset α) (event : α → Prop)
    [DecidablePred event] (hC : C.Nonempty) (hF : (C.filter event).Nonempty) (F : α → ℝ) :
    (𝔼 p ∈ C, if event p then F p else 0) =
      ((C.filter event).card : ℝ) / C.card * (𝔼 p ∈ C.filter event, F p) := by
  have hc : (C.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hC).ne'
  have hf : ((C.filter event).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hF).ne'
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_filter]
  field_simp
  <;> ring

theorem accepted_weighted_expectation (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (g : Fin m) (hg : g ∈ available reference depth)
    (F : ReplicaPS.Profile m q → ℝ) :
    (𝔼 profile ∈ fiber reference depth, rawWeight reference depth profile g * F profile) =
      (1 / (m : ℝ)) * (𝔼 profile ∈ acceptedFiber reference depth g, F profile) := by
  have hC := ReplicaChoiceMachine.pathFiber_nonempty reference depth
  have hG := acceptedFiber_nonempty reference depth hs g hg
  have hA : ((available reference depth).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (stochastic_nonempty _ hs)).ne'
  have heq (profile : ReplicaPS.Profile m q) :
      rawWeight reference depth profile g * F profile =
        ((available reference depth).card : ℝ) / m *
          (if chosenType reference depth profile = g then F profile else 0) := by
    unfold rawWeight
    simp only [hg, if_true, add_zero]
    split_ifs <;> ring
  simp_rw [heq]
  rw [← Finset.mul_expect]
  rw [expect_indicator_mul (fiber reference depth)
    (fun profile => chosenType reference depth profile = g) hC hG F]
  change ((available reference depth).card : ℝ) / m *
    (((acceptedFiber reference depth g).card : ℝ) / (fiber reference depth).card *
      (𝔼 profile ∈ acceptedFiber reference depth g, F profile)) = _
  rw [acceptedFiber_card_ratio reference depth hs g hg]
  have hcancel : ((available reference depth).card : ℝ) / m *
      (1 / ((available reference depth).card : ℝ)) = 1 / (m : ℝ) := by
    calc
      _ = (((available reference depth).card : ℝ) *
          ((available reference depth).card : ℝ)⁻¹) * (m : ℝ)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hA]; ring
  rw [← mul_assoc, hcancel]

/-- Accepting a raw label gives precisely the next concrete copy-history
fiber, rather than an independently postulated type process. -/
theorem acceptedFiber_eq_next_pathFiber (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = true)
    (g : Fin m) (hg : g ∈ available reference depth) :
    acceptedFiber reference depth g =
      ReplicaChoiceMachine.pathFiber (depth + 1)
        (representative (PSChoiceMachine.queryActive (history reference depth)) g ::
          history reference depth) := by
  ext profile
  constructor
  · intro hp
    obtain ⟨hp, htype⟩ := Finset.mem_filter.mp hp
    have hmem := (Finset.mem_filter.mp hp).1
    have hh : history profile depth = history reference depth := (Finset.mem_filter.mp hp).2
    have hA : (queryTypes (history profile depth)).Nonempty := by
      rw [hh]
      exact stochastic_nonempty _ hs
    have hans := answer_eq_representative profile depth hA
    rw [hh] at hans
    change typeOf (answer profile (history reference depth)) = g at htype
    rw [htype] at hans
    apply Finset.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    change answer profile (history profile depth) :: history profile depth = _
    rw [hh, hans]
  · intro hp
    obtain ⟨hmem, hh⟩ := Finset.mem_filter.mp hp
    change answer profile (history profile depth) :: history profile depth = _ at hh
    obtain ⟨hans, hhist⟩ := List.cons.inj hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hmem, hhist⟩, ?_⟩
    unfold chosenType
    rw [← hhist, hans]
    exact (representative_mem _ g hg).2

end ProbabilisticSerial.ReplicaRawStep
