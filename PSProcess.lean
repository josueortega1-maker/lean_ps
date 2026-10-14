import UniformPermutationProfile
import Mathlib.Data.Finset.Max

/-!
# Event-driven probabilistic serial

This file constructs the continuous probabilistic-serial eating process as a
finite event trace. Between exhaustion events all demands are constant, so the
remaining supplies are linear and the next event occurs after the minimum
supply-to-demand ratio. At least one active good is exhausted at every step.

The construction proves termination, allocation feasibility, conservation of
time and goods, the exact dynamic-rank identity, the simultaneous-rank event's
probability bound, and the deterministic rank-reduction inequality used in the
paper.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSProcess

open UniformPermutation UniformSubsetRank UniformProduct

abbrev Profile (n : ℕ) := Fin n → PreferenceOrder n

/-- The one-indexed position of a good in a strict preference order. -/
def rankOf {n : ℕ} (σ : PreferenceOrder n) (g : Fin n) : ℕ :=
  (σ.symm g).val + 1

lemma preimageFinset_nonempty {n : ℕ} (σ : PreferenceOrder n)
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    (preimageFinset σ S).Nonempty := by
  change (S.map σ.symm.toEmbedding).Nonempty
  exact Finset.Nonempty.map hS

/-- An agent's favourite good in a nonempty active set. -/
def favorite {n : ℕ} (σ : PreferenceOrder n) (S : Finset (Fin n))
    (hS : S.Nonempty) : Fin n :=
  σ ((preimageFinset σ S).min' (preimageFinset_nonempty σ hS))

lemma favorite_mem {n : ℕ} (σ : PreferenceOrder n) (S : Finset (Fin n))
    (hS : S.Nonempty) : favorite σ S hS ∈ S := by
  have hmin := (preimageFinset σ S).min'_mem
    (preimageFinset_nonempty σ hS)
  simpa [favorite, preimageFinset] using hmin

lemma fin_val_monotone {n : ℕ} : Monotone (fun i : Fin n => i.val) :=
  fun _ _ h => h

/-- The paper's static active rank is exactly the rank of the good consumed
during an eating phase. -/
theorem rankOf_favorite_eq_activeRank {n : ℕ} (σ : PreferenceOrder n)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    rankOf σ (favorite σ S hS) = activeRank S σ := by
  let P := preimageFinset σ S
  have hP : P.Nonempty := preimageFinset_nonempty σ hS
  have hPNat : (P.map Fin.valEmbedding).Nonempty := by
    exact Finset.Nonempty.map hP
  have hmin :
      (P.map Fin.valEmbedding).min' hPNat = (P.min' hP).val := by
    have hImage : (P.image (fun i : Fin n => i.val)).Nonempty :=
      hP.image (fun i : Fin n => i.val)
    have hi := Finset.min'_image fin_val_monotone P hImage
    simpa only [Finset.map_eq_image] using hi
  rw [rankOf, favorite, Equiv.symm_apply_apply]
  rw [activeRank, activePositions, firstRank, dif_pos hPNat]
  exact congrArg (fun r : ℕ => r + 1) hmin.symm

/-- Remaining supplies immediately after an exhaustion event. -/
abbrev SupplyState (n : ℕ) := Fin n → ℝ

def initialState (n : ℕ) : SupplyState n := fun _ => 1

def ValidState {n : ℕ} (q : SupplyState n) : Prop :=
  ∀ g, 0 ≤ q g

lemma initialState_valid (n : ℕ) : ValidState (initialState n) := by
  intro g
  simp [initialState]

/-- Goods with strictly positive remaining supply. -/
def activeGoods {n : ℕ} (q : SupplyState n) : Finset (Fin n) :=
  Finset.univ.filter (fun g => 0 < q g)

lemma mem_activeGoods_iff {n : ℕ} {q : SupplyState n} {g : Fin n} :
    g ∈ activeGoods q ↔ 0 < q g := by
  simp [activeGoods]

lemma activeGoods_initial (n : ℕ) :
    activeGoods (initialState n) = Finset.univ := by
  ext g
  simp [activeGoods, initialState]

/-- Agents currently eating good g. -/
def consumers {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) (g : Fin n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun i => favorite (profile i) (activeGoods q) hA = g)

/-- Number of agents currently eating good g. -/
def demand {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) (g : Fin n) : ℕ :=
  (consumers profile q hA g).card

lemma sum_demand {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    ∑ g : Fin n, demand profile q hA g = n := by
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin n))
    (fun i => favorite (profile i) (activeGoods q) hA)
    (fun _ => (1 : ℕ))
  simpa [demand, consumers] using h

lemma demand_pos_of_favorite_eq {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty)
    (i g : Fin n) (hig : favorite (profile i) (activeGoods q) hA = g) :
    0 < demand profile q hA g := by
  rw [demand, Finset.card_pos]
  exact ⟨i, by simp [consumers, hig]⟩

/-- Active goods currently receiving positive demand. -/
def demandedGoods {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) : Finset (Fin n) :=
  (activeGoods q).filter (fun g => 0 < demand profile q hA g)

lemma demandedGoods_nonempty {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    (demandedGoods profile q hA).Nonempty := by
  let a := hA.choose
  have ha : a ∈ activeGoods q := hA.choose_spec
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
  let i : Fin n := ⟨0, hn⟩
  let g := favorite (profile i) (activeGoods q) hA
  refine ⟨g, ?_⟩
  rw [demandedGoods, Finset.mem_filter]
  exact ⟨favorite_mem (profile i) (activeGoods q) hA,
    demand_pos_of_favorite_eq profile q hA i g rfl⟩

/-- Time until the next exhaustion while all current consumers eat at unit
speed. -/
def nextDelay {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) : ℝ :=
  let D := demandedGoods profile q hA
  let ratios := D.image
    (fun g => q g / (demand profile q hA g : ℝ))
  ratios.min' ((demandedGoods_nonempty profile q hA).image _)

lemma nextDelay_mem_ratios {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    nextDelay profile q hA ∈
      (demandedGoods profile q hA).image
        (fun g => q g / (demand profile q hA g : ℝ)) := by
  exact Finset.min'_mem _ _

lemma nextDelay_pos {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) :
    0 < nextDelay profile q hA := by
  obtain ⟨g, hg, hratio⟩ :=
    Finset.mem_image.mp (nextDelay_mem_ratios profile q hA)
  rw [← hratio]
  have hgA : g ∈ activeGoods q :=
    (Finset.mem_filter.mp hg).1
  have hgd : 0 < demand profile q hA g :=
    (Finset.mem_filter.mp hg).2
  exact div_pos (mem_activeGoods_iff.mp hgA) (by exact_mod_cast hgd)

lemma nextDelay_le_ratio {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty)
    {g : Fin n} (hg : g ∈ demandedGoods profile q hA) :
    nextDelay profile q hA ≤
      q g / (demand profile q hA g : ℝ) := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨g, hg, rfl⟩

/-- State immediately after the next exhaustion event. -/
def stepState {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) : SupplyState n :=
  fun g => q g -
    nextDelay profile q hA * (demand profile q hA g : ℝ)

lemma active_of_demand_pos {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) {g : Fin n}
    (hg : 0 < demand profile q hA g) :
    g ∈ activeGoods q := by
  rw [demand, Finset.card_pos] at hg
  obtain ⟨i, hi⟩ := hg
  have hchoice :
      favorite (profile i) (activeGoods q) hA = g :=
    (Finset.mem_filter.mp hi).2
  rw [← hchoice]
  exact favorite_mem (profile i) (activeGoods q) hA

lemma stepState_valid {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hq : ValidState q) (hA : (activeGoods q).Nonempty) :
    ValidState (stepState profile q hA) := by
  intro g
  by_cases hd0 : demand profile q hA g = 0
  · simp [stepState, hd0, hq g]
  · have hd : 0 < demand profile q hA g := Nat.pos_of_ne_zero hd0
    have hgD : g ∈ demandedGoods profile q hA := by
      rw [demandedGoods, Finset.mem_filter]
      exact ⟨active_of_demand_pos profile q hA hd, hd⟩
    have hdelay := nextDelay_le_ratio profile q hA hgD
    have hdR : (0 : ℝ) < demand profile q hA g := by
      exact_mod_cast hd
    have hconsumed :
        nextDelay profile q hA * (demand profile q hA g : ℝ) ≤ q g :=
      (le_div_iff₀ hdR).mp hdelay
    exact sub_nonneg.mpr hconsumed

lemma stepState_le {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hA : (activeGoods q).Nonempty) (g : Fin n) :
    stepState profile q hA g ≤ q g := by
  rw [stepState]
  exact sub_le_self _ (mul_nonneg (nextDelay_pos profile q hA).le
    (Nat.cast_nonneg _))

lemma activeGoods_step_subset {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    activeGoods (stepState profile q hA) ⊆ activeGoods q := by
  intro g hg
  rw [mem_activeGoods_iff] at hg ⊢
  exact lt_of_lt_of_le hg (stepState_le profile q hA g)

lemma exists_exhausted_at_step {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    ∃ g ∈ activeGoods q, stepState profile q hA g = 0 := by
  obtain ⟨g, hgD, hratio⟩ :=
    Finset.mem_image.mp (nextDelay_mem_ratios profile q hA)
  have hgA : g ∈ activeGoods q := (Finset.mem_filter.mp hgD).1
  have hd : 0 < demand profile q hA g := (Finset.mem_filter.mp hgD).2
  have hdR : (demand profile q hA g : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hq :
      q g = nextDelay profile q hA * (demand profile q hA g : ℝ) := by
    rw [← hratio]
    field_simp
  refine ⟨g, hgA, ?_⟩
  simp [stepState, hq]

lemma activeGoods_step_ssubset {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    activeGoods (stepState profile q hA) ⊂ activeGoods q := by
  have hsub := activeGoods_step_subset profile q hA
  rw [Finset.ssubset_iff_of_subset hsub]
  obtain ⟨g, hgA, hg0⟩ := exists_exhausted_at_step profile q hA
  refine ⟨g, hgA, ?_⟩
  rw [mem_activeGoods_iff, hg0]
  norm_num

lemma activeGoods_step_card_lt {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    (activeGoods (stepState profile q hA)).card <
      (activeGoods q).card :=
  Finset.card_lt_card (activeGoods_step_ssubset profile q hA)

def totalSupply {n : ℕ} (q : SupplyState n) : ℝ :=
  ∑ g : Fin n, q g

lemma totalSupply_initial (n : ℕ) :
    totalSupply (initialState n) = n := by
  simp [totalSupply, initialState]

lemma totalSupply_step {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hA : (activeGoods q).Nonempty) :
    totalSupply (stepState profile q hA) =
      totalSupply q - (n : ℝ) * nextDelay profile q hA := by
  have hsumNat := sum_demand profile q hA
  have hsumReal :
      (∑ g : Fin n, (demand profile q hA g : ℝ)) = (n : ℝ) := by
    exact_mod_cast hsumNat
  change (∑ g : Fin n,
      (q g - nextDelay profile q hA *
        (demand profile q hA g : ℝ))) =
    (∑ g : Fin n, q g) - (n : ℝ) * nextDelay profile q hA
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hsumReal]
  ring

/-- One interval between successive exhaustion events. -/
structure Phase (n : ℕ) (profile : Profile n) where
  before : SupplyState n
  valid : ValidState before
  active_nonempty : (activeGoods before).Nonempty

namespace Phase

def active {n : ℕ} {profile : Profile n} (p : Phase n profile) :
    Finset (Fin n) :=
  activeGoods p.before

def duration {n : ℕ} {profile : Profile n} (p : Phase n profile) : ℝ :=
  nextDelay profile p.before p.active_nonempty

def choice {n : ℕ} {profile : Profile n} (p : Phase n profile)
    (i : Fin n) : Fin n :=
  favorite (profile i) p.active p.active_nonempty

def load {n : ℕ} {profile : Profile n} (p : Phase n profile)
    (g : Fin n) : ℕ :=
  demand profile p.before p.active_nonempty g

def after {n : ℕ} {profile : Profile n} (p : Phase n profile) :
    SupplyState n :=
  stepState profile p.before p.active_nonempty

lemma duration_pos {n : ℕ} {profile : Profile n} (p : Phase n profile) :
    0 < p.duration :=
  nextDelay_pos profile p.before p.active_nonempty

lemma choice_mem_active {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) :
    p.choice i ∈ p.active :=
  favorite_mem (profile i) p.active p.active_nonempty

lemma rank_choice {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (i : Fin n) :
    rankOf (profile i) (p.choice i) = activeRank p.active (profile i) :=
  rankOf_favorite_eq_activeRank (profile i) p.active p.active_nonempty

end Phase

/-- The complete finite event trace, together with its terminal state. -/
structure RunResult (n : ℕ) (profile : Profile n) where
  phases : List (Phase n profile)
  finalState : SupplyState n
  final_valid : ValidState finalState
  final_active_empty : activeGoods finalState = ∅

/-- Execute the continuous PS eating rule from a valid remaining-supply
state. Each recursive call removes at least one active good. -/
def runFrom {n : ℕ} (profile : Profile n) (q : SupplyState n)
    (hq : ValidState q) : RunResult n profile :=
  if hA : (activeGoods q).Nonempty then
    let p : Phase n profile := ⟨q, hq, hA⟩
    let tail := runFrom profile p.after
      (stepState_valid profile q hq hA)
    { phases := p :: tail.phases
      finalState := tail.finalState
      final_valid := tail.final_valid
      final_active_empty := tail.final_active_empty }
  else
    { phases := []
      finalState := q
      final_valid := hq
      final_active_empty := Finset.not_nonempty_iff_eq_empty.mp hA }
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

/-- The PS run from unit supplies. -/
def run {n : ℕ} (profile : Profile n) : RunResult n profile :=
  runFrom profile (initialState n) (initialState_valid n)

def totalDuration {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) : ℝ :=
  (result.phases.map Phase.duration).sum

def consumedByGood {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) (g : Fin n) : ℝ :=
  (result.phases.map
    (fun p => p.duration * (p.load g : ℝ))).sum

theorem runFrom_totalSupply {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hq : ValidState q) :
    totalSupply q =
      (n : ℝ) * totalDuration (runFrom profile q hq) +
        totalSupply (runFrom profile q hq).finalState := by
  rw [runFrom]
  split
  next hA =>
    let p : Phase n profile := ⟨q, hq, hA⟩
    let hq' := stepState_valid profile q hq hA
    let tail := runFrom profile p.after hq'
    have ih := runFrom_totalSupply profile p.after hq'
    have hs := totalSupply_step profile q hA
    change totalSupply q =
      (n : ℝ) * (p.duration + totalDuration tail) +
        totalSupply tail.finalState
    change totalSupply p.after =
      (n : ℝ) * totalDuration tail + totalSupply tail.finalState at ih
    change totalSupply p.after =
      totalSupply q - (n : ℝ) * p.duration at hs
    linarith
  next hA =>
    simp [totalDuration]
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

theorem runFrom_good_conservation {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hq : ValidState q) (g : Fin n) :
    q g = consumedByGood (runFrom profile q hq) g +
      (runFrom profile q hq).finalState g := by
  rw [runFrom]
  split
  next hA =>
    let p : Phase n profile := ⟨q, hq, hA⟩
    let hq' := stepState_valid profile q hq hA
    let tail := runFrom profile p.after hq'
    have ih := runFrom_good_conservation profile p.after hq' g
    change q g =
      (p.duration * (p.load g : ℝ) + consumedByGood tail g) +
        tail.finalState g
    change p.after g =
      consumedByGood tail g + tail.finalState g at ih
    have hs : p.after g = q g - p.duration * (p.load g : ℝ) := rfl
    linarith
  next hA =>
    simp [consumedByGood]
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

lemma RunResult.finalState_eq_zero {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) :
    result.finalState = fun _ => 0 := by
  funext g
  have hnot : ¬0 < result.finalState g := by
    intro hg
    have hmem : g ∈ activeGoods result.finalState :=
      mem_activeGoods_iff.mpr hg
    rw [result.final_active_empty] at hmem
    exact Finset.not_mem_empty g hmem
  exact le_antisymm (le_of_not_gt hnot) (result.final_valid g)

theorem run_totalDuration {n : ℕ} (profile : Profile n) (hn : 0 < n) :
    totalDuration (run profile) = 1 := by
  have h := runFrom_totalSupply profile (initialState n) (initialState_valid n)
  have hfinal := (run profile).finalState_eq_zero
  change totalSupply (initialState n) =
    (n : ℝ) * totalDuration (run profile) +
      totalSupply (run profile).finalState at h
  rw [totalSupply_initial, hfinal] at h
  simp only [totalSupply, Pi.zero_apply, Finset.sum_const_zero, add_zero] at h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ hnR)
  simpa using h.symm

theorem run_consumedByGood {n : ℕ} (profile : Profile n) (g : Fin n) :
    consumedByGood (run profile) g = 1 := by
  have h := runFrom_good_conservation profile
    (initialState n) (initialState_valid n) g
  have hfinal := (run profile).finalState_eq_zero
  change initialState n g =
    consumedByGood (run profile) g + (run profile).finalState g at h
  rw [hfinal] at h
  simpa [initialState] using h.symm

theorem runFrom_phases_length_le {n : ℕ} (profile : Profile n)
    (q : SupplyState n) (hq : ValidState q) :
    (runFrom profile q hq).phases.length ≤ (activeGoods q).card := by
  rw [runFrom]
  split
  next hA =>
    have ih := runFrom_phases_length_le profile
      (stepState profile q hA) (stepState_valid profile q hq hA)
    have hdrop := activeGoods_step_card_lt profile q hA
    simp only [List.length_cons, Phase.after]
    omega
  next hA =>
    simp
termination_by (activeGoods q).card
decreasing_by
  apply activeGoods_step_card_lt

/-- At least one good disappears in every phase, so a run has at most `n`
phases. -/
theorem run_phases_length_le {n : ℕ} (profile : Profile n) :
    (run profile).phases.length ≤ n := by
  have h := runFrom_phases_length_le profile
    (initialState n) (initialState_valid n)
  simpa [run, activeGoods_initial] using h

/-- Allocation generated by a finite list of PS phases. -/
def allocationFrom {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) (i g : Fin n) : ℝ :=
  (phases.map (fun p => if p.choice i = g then p.duration else 0)).sum

def allocation {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) (i g : Fin n) : ℝ :=
  allocationFrom result.phases i g

lemma allocationFrom_agent_sum {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) (i : Fin n) :
    (∑ g : Fin n, allocationFrom phases i g) =
      (phases.map Phase.duration).sum := by
  induction phases with
  | nil => simp [allocationFrom]
  | cons p phases ih =>
      change (∑ g : Fin n,
        ((if p.choice i = g then p.duration else 0) +
          allocationFrom phases i g)) =
        p.duration + (phases.map Phase.duration).sum
      rw [Finset.sum_add_distrib, ih]
      simp

theorem run_allocation_agent_sum {n : ℕ} (profile : Profile n)
    (hn : 0 < n) (i : Fin n) :
    (∑ g : Fin n, allocation (run profile) i g) = 1 := by
  change (∑ g : Fin n, allocationFrom (run profile).phases i g) = 1
  rw [allocationFrom_agent_sum]
  exact run_totalDuration profile hn

lemma phase_choice_mass {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (g : Fin n) :
    (∑ i : Fin n, if p.choice i = g then p.duration else 0) =
      p.duration * (p.load g : ℝ) := by
  have hcountNat :
      (∑ i : Fin n, if p.choice i = g then 1 else 0) = p.load g := by
    rw [Finset.sum_boole]
    change (Finset.univ.filter (fun i => p.choice i = g)).card =
      (Finset.univ.filter (fun i =>
        favorite (profile i) (activeGoods p.before)
          p.active_nonempty = g)).card
    congr 1
  have hcountReal :
      (∑ i : Fin n, if p.choice i = g then (1 : ℝ) else 0) =
        (p.load g : ℝ) := by
    exact_mod_cast hcountNat
  calc
    (∑ i : Fin n, if p.choice i = g then p.duration else 0) =
        ∑ i : Fin n,
          p.duration * (if p.choice i = g then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split <;> simp_all
    _ = p.duration *
        (∑ i : Fin n, if p.choice i = g then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
    _ = p.duration * (p.load g : ℝ) := by rw [hcountReal]

lemma allocationFrom_good_sum {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) (g : Fin n) :
    (∑ i : Fin n, allocationFrom phases i g) =
      (phases.map (fun p => p.duration * (p.load g : ℝ))).sum := by
  induction phases with
  | nil => simp [allocationFrom]
  | cons p phases ih =>
      change (∑ i : Fin n,
        ((if p.choice i = g then p.duration else 0) +
          allocationFrom phases i g)) =
        p.duration * (p.load g : ℝ) +
          (phases.map (fun p => p.duration * (p.load g : ℝ))).sum
      rw [Finset.sum_add_distrib, phase_choice_mass, ih]

theorem run_allocation_good_sum {n : ℕ} (profile : Profile n)
    (g : Fin n) :
    (∑ i : Fin n, allocation (run profile) i g) = 1 := by
  change (∑ i : Fin n, allocationFrom (run profile).phases i g) = 1
  rw [allocationFrom_good_sum]
  exact run_consumedByGood profile g

/-- Average ordinal rank of the allocation generated by a run. -/
def averageRank {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ i : Fin n, ∑ g : Fin n,
      (rankOf (profile i) g : ℝ) * allocation result i g

/-- Event-driven form of the paper's integral of the mean active rank. -/
def dynamicRank {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) : ℝ :=
  (1 / (n : ℝ)) *
    (result.phases.map (fun p =>
      p.duration * ∑ i : Fin n,
        (activeRank p.active (profile i) : ℝ))).sum

lemma phase_weighted_rank {n : ℕ} {profile : Profile n}
    (p : Phase n profile) :
    (∑ i : Fin n, ∑ g : Fin n,
      (rankOf (profile i) g : ℝ) *
        (if p.choice i = g then p.duration else 0)) =
      p.duration * ∑ i : Fin n,
        (activeRank p.active (profile i) : ℝ) := by
  have hi (i : Fin n) :
      (∑ g : Fin n, (rankOf (profile i) g : ℝ) *
        (if p.choice i = g then p.duration else 0)) =
        p.duration * (activeRank p.active (profile i) : ℝ) := by
    calc
      (∑ g : Fin n, (rankOf (profile i) g : ℝ) *
          (if p.choice i = g then p.duration else 0)) =
          (rankOf (profile i) (p.choice i) : ℝ) * p.duration := by
        simp
      _ = p.duration * (activeRank p.active (profile i) : ℝ) := by
        rw [p.rank_choice i]
        ring
  calc
    (∑ i : Fin n, ∑ g : Fin n,
      (rankOf (profile i) g : ℝ) *
        (if p.choice i = g then p.duration else 0)) =
        ∑ i : Fin n,
          p.duration * (activeRank p.active (profile i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi_mem
      exact hi i
    _ = p.duration * ∑ i : Fin n,
        (activeRank p.active (profile i) : ℝ) := by
      rw [Finset.mul_sum]

lemma weightedRank_allocationFrom {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) :
    (∑ i : Fin n, ∑ g : Fin n,
      (rankOf (profile i) g : ℝ) * allocationFrom phases i g) =
      (phases.map (fun p =>
        p.duration * ∑ i : Fin n,
          (activeRank p.active (profile i) : ℝ))).sum := by
  induction phases with
  | nil => simp [allocationFrom]
  | cons p phases ih =>
      change (∑ i : Fin n, ∑ g : Fin n,
        (rankOf (profile i) g : ℝ) *
          ((if p.choice i = g then p.duration else 0) +
            allocationFrom phases i g)) =
        p.duration * ∑ i : Fin n,
          (activeRank p.active (profile i) : ℝ) +
          (phases.map (fun p =>
            p.duration * ∑ i : Fin n,
              (activeRank p.active (profile i) : ℝ))).sum
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [phase_weighted_rank, ih]

/-- Exact dynamic-rank identity: the allocation's average ordinal rank is the
time sum of the mean rank of the currently consumed goods. -/
theorem averageRank_eq_dynamicRank {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) :
    averageRank result = dynamicRank result := by
  unfold averageRank dynamicRank allocation
  rw [weightedRank_allocationFrom]

/-- Event-driven form of `∫₀¹ n / |A(t)| dt`: the active set is constant
inside each phase. -/
def eatingIntegral {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) : ℝ :=
  (result.phases.map (fun p =>
    p.duration * ((n : ℝ) / (p.active.card : ℝ)))).sum

/-- The simultaneous static active-rank event furnished by Step 3. -/
def UniformRankGood {n : ℕ} (profile : Profile n) (K : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty →
    (∑ i : Fin n, scaledActiveRank n S (profile i)) < K * n

noncomputable instance instDecidableUniformRankGood {n : ℕ}
    (profile : Profile n) (K : ℝ) : Decidable (UniformRankGood profile K) :=
  Classical.propDecidable _

lemma uniformRankGood_iff_not_failure {n : ℕ} (profile : Profile n)
    (K : ℝ) :
    UniformRankGood profile K ↔
      ¬∃ S ∈ nonemptyActiveSets n,
        K * n ≤ ∑ i : Fin n, scaledActiveRank n S (profile i) := by
  constructor
  · intro hgood hbad
    obtain ⟨S, hS, hlarge⟩ := hbad
    exact (not_le_of_gt
      (hgood S (mem_nonemptyActiveSets_iff.mp hS))) hlarge
  · intro hnot S hS
    apply lt_of_not_ge
    intro hlarge
    exact hnot ⟨S, mem_nonemptyActiveSets_iff.mpr hS, hlarge⟩

/-- Step 3's simultaneous permutation bound, restated as the failure
probability of the good event used by the concrete PS trajectory. -/
theorem uniformRankGood_failure_probability_le {n : ℕ} (hn : 0 < n)
    {K c : ℝ}
    (hK : Real.log 2 + c ≤
      (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1)) :
    probability (preferenceProfileSample n)
        (fun profile => ¬UniformRankGood profile K) ≤
      Real.exp (-c * n) := by
  classical
  simpa only [uniformRankGood_iff_not_failure, not_not] using
    (uniform_active_rank_exponential_profile hn hK)

lemma phase_averageRank_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {K : ℝ} (hgood : UniformRankGood profile K)
    (p : Phase n profile) :
    (1 / (n : ℝ)) *
        (∑ i : Fin n, (activeRank p.active (profile i) : ℝ)) ≤
      K * ((n : ℝ) / (p.active.card : ℝ)) := by
  let N : ℝ := n
  let s : ℝ := p.active.card
  let R : ℝ := ∑ i : Fin n,
    (activeRank p.active (profile i) : ℝ)
  have hnR : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hsNat : 0 < p.active.card := Finset.card_pos.mpr p.active_nonempty
  have hsR : 0 < s := by
    dsimp [s]
    exact_mod_cast hsNat
  have hscaled := hgood p.active p.active_nonempty
  simp only [scaledActiveRank] at hscaled
  rw [← Finset.mul_sum] at hscaled
  have hscaled' : (s / N) * R ≤ K * N := by
    exact le_of_lt hscaled
  rw [div_mul_eq_mul_div] at hscaled'
  have hproduct : s * R ≤ (K * N) * N :=
    (div_le_iff₀ hnR).mp hscaled'
  have hquotient : R / N ≤ (K * N) / s := by
    apply (div_le_div_iff₀ hnR hsR).2
    simpa [mul_comm] using hproduct
  change (1 / N) * R ≤ K * (N / s)
  calc
    (1 / N) * R = R / N := by ring
    _ ≤ (K * N) / s := hquotient
    _ = K * (N / s) := by ring

lemma phase_rank_contribution_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {K : ℝ} (hgood : UniformRankGood profile K)
    (p : Phase n profile) :
    p.duration * ((1 / (n : ℝ)) *
        (∑ i : Fin n, (activeRank p.active (profile i) : ℝ))) ≤
      K * (p.duration * ((n : ℝ) / (p.active.card : ℝ))) := by
  have h := mul_le_mul_of_nonneg_left
    (phase_averageRank_le hn hgood p) p.duration_pos.le
  calc
    p.duration * ((1 / (n : ℝ)) *
        (∑ i : Fin n, (activeRank p.active (profile i) : ℝ))) ≤
        p.duration * (K * ((n : ℝ) / (p.active.card : ℝ))) := h
    _ = K * (p.duration * ((n : ℝ) / (p.active.card : ℝ))) := by
      ring

lemma dynamicRank_eq_phase_sum {n : ℕ} {profile : Profile n}
    (result : RunResult n profile) :
    dynamicRank result =
      (result.phases.map (fun p =>
        p.duration * ((1 / (n : ℝ)) *
          ∑ i : Fin n,
            (activeRank p.active (profile i) : ℝ)))).sum := by
  unfold dynamicRank
  induction result.phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [← ih]
      ring

lemma phase_rank_sum_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {K : ℝ} (hgood : UniformRankGood profile K)
    (phases : List (Phase n profile)) :
    (phases.map (fun p =>
      p.duration * ((1 / (n : ℝ)) *
        ∑ i : Fin n,
          (activeRank p.active (profile i) : ℝ)))).sum ≤
      (phases.map (fun p =>
        K * (p.duration * ((n : ℝ) / (p.active.card : ℝ))))).sum := by
  induction phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (phase_rank_contribution_le hn hgood p) ih

lemma sum_phase_integral_mul {n : ℕ} {profile : Profile n}
    (K : ℝ) (phases : List (Phase n profile)) :
    (phases.map (fun p =>
      K * (p.duration * ((n : ℝ) / (p.active.card : ℝ))))).sum =
      K * (phases.map (fun p =>
        p.duration * ((n : ℝ) / (p.active.card : ℝ)))).sum := by
  induction phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- Deterministic rank reduction for any event-driven PS trace. -/
theorem dynamicRank_le_eatingIntegral {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {K : ℝ} (hgood : UniformRankGood profile K)
    (result : RunResult n profile) :
    dynamicRank result ≤ K * eatingIntegral result := by
  rw [dynamicRank_eq_phase_sum]
  calc
    (result.phases.map (fun p =>
      p.duration * ((1 / (n : ℝ)) *
        ∑ i : Fin n,
          (activeRank p.active (profile i) : ℝ)))).sum ≤
        (result.phases.map (fun p =>
          K * (p.duration *
            ((n : ℝ) / (p.active.card : ℝ))))).sum :=
      phase_rank_sum_le hn hgood result.phases
    _ = K * eatingIntegral result := by
      rw [sum_phase_integral_mul]
      rfl

/-- The paper's rank-reduction inequality for the concrete PS run. -/
theorem run_rankReduction {n : ℕ} (profile : Profile n) (hn : 0 < n)
    {K : ℝ} (hgood : UniformRankGood profile K) :
    averageRank (run profile) ≤ K * eatingIntegral (run profile) := by
  rw [averageRank_eq_dynamicRank]
  exact dynamicRank_le_eatingIntegral hn hgood (run profile)

lemma allocationFrom_nonneg {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) (i g : Fin n) :
    0 ≤ allocationFrom phases i g := by
  induction phases with
  | nil => simp [allocationFrom]
  | cons p phases ih =>
      change 0 ≤ (if p.choice i = g then p.duration else 0) +
        allocationFrom phases i g
      apply add_nonneg
      · split
        · exact p.duration_pos.le
        · exact le_rfl
      · exact ih

lemma run_allocation_nonneg {n : ℕ} (profile : Profile n) (i g : Fin n) :
    0 ≤ allocation (run profile) i g :=
  allocationFrom_nonneg (run profile).phases i g

lemma rankOf_le_marketSize {n : ℕ} (σ : PreferenceOrder n) (g : Fin n) :
    rankOf σ g ≤ n := by
  unfold rankOf
  omega

lemma run_agent_rank_le_marketSize {n : ℕ} (profile : Profile n)
    (hn : 0 < n) (i : Fin n) :
    (∑ g : Fin n, (rankOf (profile i) g : ℝ) *
      allocation (run profile) i g) ≤ n := by
  have hpoint (g : Fin n) :
      (rankOf (profile i) g : ℝ) * allocation (run profile) i g ≤
        (n : ℝ) * allocation (run profile) i g := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast rankOf_le_marketSize (profile i) g
    · exact run_allocation_nonneg profile i g
  calc
    (∑ g : Fin n, (rankOf (profile i) g : ℝ) *
      allocation (run profile) i g) ≤
        ∑ g : Fin n, (n : ℝ) * allocation (run profile) i g := by
      apply Finset.sum_le_sum
      intro g hg
      exact hpoint g
    _ = (n : ℝ) *
        (∑ g : Fin n, allocation (run profile) i g) := by
      rw [Finset.mul_sum]
    _ = n := by rw [run_allocation_agent_sum profile hn i, mul_one]

/-- The concrete PS average rank is bounded by the market size. This discharges
the deterministic bounded-rank input used in the final expectation split. -/
theorem run_averageRank_le_marketSize {n : ℕ} (profile : Profile n)
    (hn : 0 < n) :
    averageRank (run profile) ≤ n := by
  have htotal :
      (∑ i : Fin n, ∑ g : Fin n,
        (rankOf (profile i) g : ℝ) * allocation (run profile) i g) ≤
        (n : ℝ) * (n : ℝ) := by
    calc
      (∑ i : Fin n, ∑ g : Fin n,
        (rankOf (profile i) g : ℝ) * allocation (run profile) i g) ≤
          ∑ _i : Fin n, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact run_agent_rank_le_marketSize profile hn i
      _ = (n : ℝ) * (n : ℝ) := by simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold averageRank
  calc
    (1 / (n : ℝ)) *
      (∑ i : Fin n, ∑ g : Fin n,
        (rankOf (profile i) g : ℝ) * allocation (run profile) i g) ≤
        (1 / (n : ℝ)) * ((n : ℝ) * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = n := by field_simp

end ProbabilisticSerial.PSProcess
