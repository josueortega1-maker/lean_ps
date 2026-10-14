import ReplicaRank
import ReplicaRevelation

/-!
# Fresh type selections in the concrete replica eating trace

An internal exhaustion of a copy is not a fresh type choice. The persistence
lemma below characterizes exactly when an agent's selected type can change.
The adaptive replay/fiber theorem is provided in ReplicaChoiceMachine, and
ReplicaHistory and ReplicaLaw connect the conditional law to the PS path.
-/

noncomputable section

open Finset

namespace ProbabilisticSerial.ReplicaTrace

open UniformPermutation PSProcess ReplicaPS ReplicaRank ReplicaRevelation

lemma favorite_persists {m : ℕ} (σ : PreferenceOrder m)
    {S T : Finset (Fin m)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hTS : T ⊆ S) (hkeep : favorite σ S hS ∈ T) :
    favorite σ T hT = favorite σ S hS := by
  have h1 := favorite_rank_le σ T hT _ hkeep
  have h2 := favorite_rank_le σ S hS _ (hTS (favorite_mem σ T hT))
  have heq : (σ.symm (favorite σ T hT)).val = (σ.symm (favorite σ S hS)).val := by
    unfold rankOf at h1 h2
    omega
  exact σ.symm.injective (Fin.ext heq)

lemma type_choice {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) (i : Fin (m * q)) :
    typeOf (p.choice i) = favorite (profile i) (activeTypes p) (activeTypes_nonempty p) :=
  favorite_type (profile i) p.active p.active_nonempty

theorem choice_changes_iff_type_exhausted {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (earlier later : ReplicaPhase profile) (i : Fin (m * q))
    (hnested : later.active ⊆ earlier.active) :
    typeOf (later.choice i) ≠ typeOf (earlier.choice i) ↔
      typeOf (earlier.choice i) ∉ activeTypes later := by
  have hsub : activeTypes later ⊆ activeTypes earlier := Finset.image_subset_image hnested
  have hlmem : typeOf (later.choice i) ∈ activeTypes later :=
    Finset.mem_image.mpr ⟨later.choice i, later.choice_mem_active i, rfl⟩
  constructor
  · intro hne hkeep
    apply hne
    rw [type_choice, type_choice]
    apply favorite_persists _ _ _ hsub
    simpa only [type_choice] using hkeep
  · intro hex heq
    exact hex (heq ▸ hlmem)

theorem run_activeTypes_pairwise {m q : ℕ} (profile : ReplicaPS.Profile m q) :
    (run (liftedProfile profile)).phases.Pairwise
      (fun earlier later => activeTypes later ⊆ activeTypes earlier) := by
  apply (SequentialRevelation.run_phases_pairwise (liftedProfile profile)).imp
  intro earlier later h
  exact Finset.image_subset_image h.1

def phaseReveal {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) (i : Fin (m * q)) : Reveal m q :=
  ⟨i, activeTypes p, typeOf (p.choice i),
    Finset.mem_image.mpr ⟨p.choice i, p.choice_mem_active i, rfl⟩⟩

lemma phaseReveal_compatible {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) (i : Fin (m * q)) :
    Compatible profile [phaseReveal p i] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (type_choice p i).symm

def Fresh {m q : ℕ} (history : RevealHistory m q)
    (agent : Fin (m * q)) (available : Finset (Fin m)) : Prop :=
  ∀ r ∈ history, r.agent = agent → r.chosen ∉ available

theorem fresh_phase_query_admissible {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) (history : RevealHistory m q) (i : Fin (m * q))
    (hnested : ∀ r ∈ history, r.agent = i → activeTypes p ⊆ r.available)
    (hfresh : Fresh history i (activeTypes p)) :
    AdmissibleQuery history i (activeTypes p) := by
  intro r hr hi g hg
  exact Finset.mem_erase.mpr
    ⟨fun h => hfresh r hr hi (h ▸ hg), hnested r hr hi hg⟩

/-- Within a surviving type no new type query should be recorded. -/
theorem retained_type_not_fresh {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (earlier later : ReplicaPhase profile) (history : RevealHistory m q)
    (i : Fin (m * q)) (hrecord : phaseReveal earlier i ∈ history)
    (hkeep : typeOf (earlier.choice i) ∈ activeTypes later) :
    ¬Fresh history i (activeTypes later) := by
  intro h
  exact h (phaseReveal earlier i) hrecord rfl hkeep

end ProbabilisticSerial.ReplicaTrace
