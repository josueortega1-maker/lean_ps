import ReplicaLaw
import PSFiniteCapacity

/-! Type capacities, consumption, and the unchanged clock of the ordered-copy run. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaChoiceMachine
open UniformPermutation PSProcess ReplicaPS PSChoiceMachine
variable {m q : ℕ} [Nonempty (Fin (m * q))]
include m q

abbrev roundTime (profile : ReplicaPS.Profile m q) := PSChoiceMachine.roundTime (liftedProfile profile)
abbrev roundDuration (profile : ReplicaPS.Profile m q) := PSChoiceMachine.roundDuration (liftedProfile profile)
abbrev partialDuration (profile : ReplicaPS.Profile m q) := PSChoiceMachine.partialDuration (liftedProfile profile)

lemma type_count_pos : 0 < m := by
  have h := market_pos (n := m * q)
  by_contra hn
  have hm : m = 0 := by omega
  simp [hm] at h
lemma quota_pos : 0 < q := by
  have h := market_pos (n := m * q)
  by_contra hn
  have hq : q = 0 := by omega
  simp [hq] at h

lemma roundTime_zero (p : ReplicaPS.Profile m q) : roundTime p 0 = 0 := PSChoiceMachine.roundTime_zero _
lemma roundTime_terminal (p : ReplicaPS.Profile m q) : roundTime p (m * q) = 1 :=
  PSChoiceMachine.roundTime_terminal _
lemma roundTime_nonneg (p : ReplicaPS.Profile m q) (r : ℕ) : 0 ≤ roundTime p r :=
  PSChoiceMachine.roundTime_nonneg _ _
lemma roundTime_le_one (p : ReplicaPS.Profile m q) (r : ℕ) : roundTime p r ≤ 1 :=
  PSChoiceMachine.roundTime_le_one _ _
lemma roundTime_mono (p : ReplicaPS.Profile m q) : Monotone (roundTime p) :=
  PSChoiceMachine.roundTime_mono _
lemma roundTime_lt_one_iff (p : ReplicaPS.Profile m q) (r : ℕ) :
    roundTime p r < 1 ↔ (roundTypes p r).Nonempty := by
  rw [PSChoiceMachine.roundTime_lt_one_iff]
  exact Finset.image_nonempty.symm
lemma queryTime_at_slot (p : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q)) :
    queryTime (history p (r * (m * q) + i.val)) = roundTime p r :=
  PSChoiceMachine.queryTime_at_slot _ _ _
lemma partialDuration_eq_ramp (p : ReplicaPS.Profile m q) (t : ℝ) (r : ℕ) :
    partialDuration p t r = max (t - roundTime p r) 0 - max (t - roundTime p (r + 1)) 0 :=
  PSChoiceMachine.partialDuration_eq_ramp _ _ _

def roundChoice (p : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q)) : Fin m :=
  typeOf (PSChoiceMachine.roundChoice (liftedProfile p) r i)

lemma roundChoice_eq (p : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes p r).Nonempty) :
    roundChoice p r i = favorite (p i) (roundTypes p r) hA :=
  answer_type_at_slot p r i hA

lemma roundTypes_initial (p : ReplicaPS.Profile m q) : roundTypes p 0 = Finset.univ := by
  ext g
  simp only [roundTypes, profileSupply, activeGoods_initial, Finset.mem_image,
    Finset.mem_univ, true_and, iff_true]
  exact ⟨copyOf g ⟨0, quota_pos (m := m) (q := q)⟩, typeOf_copyOf _ _⟩

def partialConsumption (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) : ℝ :=
  ∑ k : Fin q, PSChoiceMachine.partialConsumption (liftedProfile p) t (copyOf g k)

def residual (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) : ℝ :=
  ∑ k : Fin q, PSChoiceMachine.residual (liftedProfile p) t (copyOf g k)

lemma residual_eq (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) :
    residual p t g = q - partialConsumption p t g := by
  simp [residual, PSChoiceMachine.residual, Finset.sum_sub_distrib, partialConsumption]

lemma residual_nonneg (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) : 0 ≤ residual p t g :=
  Finset.sum_nonneg (fun k _ => PSChoiceMachine.residual_nonneg _ _ _)

lemma residual_le_quota (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) : residual p t g ≤ q := by
  calc
    _ ≤ ∑ _k : Fin q, (1 : ℝ) := Finset.sum_le_sum (fun k _ => PSChoiceMachine.residual_le_one _ _ _)
    _ = _ := by simp

lemma sum_residual (p : ReplicaPS.Profile m q) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ g : Fin m, residual p t g = (m : ℝ) * q * (1 - t) := by
  unfold residual
  rw [sum_copies, PSChoiceMachine.sum_residual _ t ht ht1, Nat.cast_mul]

lemma residual_pos_implies_active (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m)
    (hg : 0 < residual p t g) (r : ℕ) (hr : r ≤ m * q) (ht : roundTime p r ≤ t) :
    g ∈ roundTypes p r := by
  have hex : ∃ k : Fin q, 0 < PSChoiceMachine.residual (liftedProfile p) t (copyOf g k) := by
    by_contra h
    push_neg at h
    have hs := Finset.sum_nonpos (fun k (_ : k ∈ (Finset.univ : Finset (Fin q))) => h k)
    exact (not_le_of_gt hg) hs
  obtain ⟨k, hpos⟩ := hex
  exact Finset.mem_image.mpr ⟨copyOf g k,
    PSChoiceMachine.residual_pos_implies_active _ t _ hpos r hr ht, typeOf_copyOf _ _⟩

lemma exists_last_survivor (p : ReplicaPS.Profile m q) :
    ∃ g : Fin m, ∀ r, roundTime p r < 1 → g ∈ roundTypes p r := by
  obtain ⟨c, hc⟩ := PSChoiceMachine.exists_last_survivor (liftedProfile p)
  exact ⟨typeOf c, fun r hr => Finset.mem_image.mpr ⟨c, hc r hr, rfl⟩⟩

def choiceIndicator (p : ReplicaPS.Profile m q) (i : Fin (m * q)) (g : Fin m) (r : ℕ) : ℝ :=
  if roundChoice p r i = g then 1 else 0

lemma sum_copy_indicator (c : Fin (m * q)) (g : Fin m) :
    (∑ k : Fin q, if c = copyOf g k then (1 : ℝ) else 0) = if typeOf c = g then 1 else 0 := by
  obtain ⟨⟨g', k'⟩, rfl⟩ := finProdFinEquiv.surjective c
  change (∑ k : Fin q, if copyOf g' k' = copyOf g k then (1 : ℝ) else 0) = _
  simp only [copyOf, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h : g' = g
  · subst g'
    simp [typeOf]
  · simp [h, typeOf]

lemma partialConsumption_eq (p : ReplicaPS.Profile m q) (t : ℝ) (g : Fin m) :
    partialConsumption p t g = ∑ r ∈ Finset.range (m * q),
      partialDuration p t r * ∑ i : Fin (m * q), choiceIndicator p i g r := by
  unfold partialConsumption PSChoiceMachine.partialConsumption
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum]
  congr 1
  simp only [choiceDemand, choiceConsumers, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_copy_indicator _ g

end ProbabilisticSerial.ReplicaChoiceMachine
