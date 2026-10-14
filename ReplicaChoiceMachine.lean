import ReplicaTrace
import PSFiniteClock
import PSRankIncrement

/-! Fresh type observations of the concrete ordered-copy PS machine. -/

noncomputable section
set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaChoiceMachine

open UniformPermutation PSProcess ReplicaPS ReplicaRevelation
open PSChoiceMachine

lemma favorite_congr_set {n : ℕ} (σ : PreferenceOrder n)
    (S T : Finset (Fin n)) (hS : S.Nonempty) (hT : T.Nonempty) (h : S = T) :
    favorite σ S hS = favorite σ T hT := by
  subst T
  rfl

variable {m q : ℕ} [Nonempty (Fin (m * q))]

abbrev history (profile : ReplicaPS.Profile m q) (depth : ℕ) :=
  profileHistory (liftedProfile profile) depth

def queryTypes (h : List (Fin (m * q))) : Finset (Fin m) :=
  (queryActive h).image typeOf

def roundTypes (profile : ReplicaPS.Profile m q) (r : ℕ) : Finset (Fin m) :=
  (activeGoods (profileSupply (liftedProfile profile) r)).image typeOf

def previousType (h : List (Fin (m * q))) : Option (Fin m) :=
  (previousChoice h).map typeOf

def FreshQuery (h : List (Fin (m * q))) : Prop :=
  match previousType h with
  | none => True
  | some g => g ∉ queryTypes h

def stochasticRecording (h : List (Fin (m * q))) : Bool :=
  by classical exact decide ((queryTypes h).Nonempty ∧ FreshQuery h)

abbrev answer (profile : ReplicaPS.Profile m q) (h : List (Fin (m * q))) :=
  profileAnswer (liftedProfile profile) h

lemma queryTypes_at_depth (profile : ReplicaPS.Profile m q) (depth : ℕ) :
    queryTypes (history profile depth) = roundTypes profile (depth / (m * q)) := by
  unfold queryTypes queryActive roundTypes history
  rw [(profile_machine_correspondence (liftedProfile profile) depth).1]

lemma queryTypes_at_slot (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q)) :
    queryTypes (history profile (r * (m * q) + i.val)) = roundTypes profile r := by
  rw [queryTypes_at_depth, round_slot_div]

lemma roundTypes_subset (profile : ReplicaPS.Profile m q) {a b : ℕ} (hab : a ≤ b) :
    roundTypes profile b ⊆ roundTypes profile a :=
  Finset.image_subset_image (profileSupply_active_subset_of_le (liftedProfile profile) hab)

lemma answer_type (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hA : (queryTypes (history profile depth)).Nonempty) :
    typeOf (answer profile (history profile depth)) =
      favorite (profile (queryAgent (history profile depth)))
        (queryTypes (history profile depth)) hA := by
  have hc : (queryActive (history profile depth)).Nonempty := Finset.image_nonempty.mp hA
  have hs := (profile_machine_correspondence (liftedProfile profile) depth).1
  have hn : (activeGoods (profileSupply (liftedProfile profile) (depth / (m * q)))).Nonempty := by
    simpa only [queryActive, hs] using hc
  rw [answer, (profile_machine_correspondence (liftedProfile profile) depth).2 hn]
  rw [liftedProfile, favorite_type]
  apply favorite_congr_set
  exact (queryTypes_at_depth profile depth).symm

lemma answer_copy_mem (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hA : (queryTypes (history profile depth)).Nonempty) :
    answer profile (history profile depth) ∈ queryActive (history profile depth) := by
  have hc : (queryActive (history profile depth)).Nonempty := Finset.image_nonempty.mp hA
  have hs := (profile_machine_correspondence (liftedProfile profile) depth).1
  have hn : (activeGoods (profileSupply (liftedProfile profile) (depth / (m * q)))).Nonempty := by
    simpa only [queryActive, hs] using hc
  rw [answer, (profile_machine_correspondence (liftedProfile profile) depth).2 hn]
  simpa only [queryActive, hs] using favorite_mem
    ((liftedProfile profile) (queryAgent (history profile depth))) _ hn

/-- Copy order within a type does not depend on its preference position. -/
lemma copy_rank_le_iff (σ : PreferenceOrder m) (c d : Fin (m * q))
    (ht : typeOf c = typeOf d) :
    rankOf (liftPreference σ) c ≤ rankOf (liftPreference σ) d ↔ c.val ≤ d.val := by
  obtain ⟨⟨g, k⟩, rfl⟩ := finProdFinEquiv.surjective c
  obtain ⟨⟨g', k'⟩, rfl⟩ := finProdFinEquiv.surjective d
  change typeOf (copyOf g k) = typeOf (copyOf g' k') at ht
  simp only [typeOf_copyOf] at ht
  subst g'
  change rankOf (liftPreference σ) (copyOf g k) ≤
    rankOf (liftPreference σ) (copyOf g k') ↔ _
  rw [rankOf_copy, rankOf_copy]
  change k.val + q * (σ.symm g).val + 1 ≤ k'.val + q * (σ.symm g).val + 1 ↔
    k.val + q * g.val ≤ k'.val + q * g.val
  omega

def representative (S : Finset (Fin (m * q))) (g : Fin m) : Fin (m * q) :=
  if h : (S.filter (fun c => typeOf c = g)).Nonempty then
    (S.filter (fun c => typeOf c = g)).min' h
  else defaultGood

lemma representative_mem (S : Finset (Fin (m * q))) (g : Fin m)
    (hg : g ∈ S.image typeOf) : representative S g ∈ S ∧ typeOf (representative S g) = g := by
  have h : (S.filter (fun c => typeOf c = g)).Nonempty := by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩
  unfold representative
  rw [dif_pos h]
  exact Finset.mem_filter.mp (Finset.min'_mem _ h)

lemma favorite_eq_representative (σ : PreferenceOrder m)
    (S : Finset (Fin (m * q))) (hS : S.Nonempty) :
    favorite (liftPreference σ) S hS =
      representative S (typeOf (favorite (liftPreference σ) S hS)) := by
  let c := favorite (liftPreference σ) S hS
  have hc : c ∈ S := favorite_mem _ _ _
  have h : (S.filter (fun d => typeOf d = typeOf c)).Nonempty :=
    ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩
  change c = representative S (typeOf c)
  unfold representative
  rw [dif_pos h]
  let d := (S.filter (fun d => typeOf d = typeOf c)).min' h
  have hd := Finset.mem_filter.mp (Finset.min'_mem _ h)
  have hmin := Finset.min'_le (S.filter (fun d => typeOf d = typeOf c)) c
    (Finset.mem_filter.mpr ⟨hc, rfl⟩)
  have hrev := (copy_rank_le_iff σ c d hd.2.symm).mp (favorite_rank_le _ S hS d hd.1)
  apply Fin.ext
  exact Nat.le_antisymm hrev hmin

lemma answer_eq_representative (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hA : (queryTypes (history profile depth)).Nonempty) :
    answer profile (history profile depth) = representative (queryActive (history profile depth))
      (typeOf (answer profile (history profile depth))) := by
  have hs := (profile_machine_correspondence (liftedProfile profile) depth).1
  have hc : (queryActive (history profile depth)).Nonempty := Finset.image_nonempty.mp hA
  have hn : (activeGoods (profileSupply (liftedProfile profile) (depth / (m * q)))).Nonempty := by
    simpa only [queryActive, hs] using hc
  rw [answer, (profile_machine_correspondence (liftedProfile profile) depth).2 hn]
  simpa only [queryActive, hs, liftedProfile] using favorite_eq_representative
    (profile (queryAgent (history profile depth))) _ hn


lemma previousType_at_slot_zero (profile : ReplicaPS.Profile m q) (i : Fin (m * q)) :
    previousType (history profile i.val) = none := by
  rw [previousType, history, previousChoice_at_slot_zero]
  rfl

lemma previousType_at_slot_succ (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes profile (r + 1)).Nonempty) :
    previousType (history profile ((r + 1) * (m * q) + i.val)) =
      some (favorite (profile i) (roundTypes profile r)
        (hA.mono (roundTypes_subset profile (Nat.le_succ r)))) := by
  have hc : (activeGoods (profileSupply (liftedProfile profile) (r + 1))).Nonempty :=
    Finset.image_nonempty.mp hA
  rw [previousType, history, previousChoice_at_slot_succ _ r i hc]
  change some (typeOf (favorite (liftPreference (profile i)) _ _)) = _
  rw [favorite_type]
  rfl

lemma answer_type_at_slot (profile : ReplicaPS.Profile m q) (r : ℕ) (i : Fin (m * q))
    (hA : (roundTypes profile r).Nonempty) :
    typeOf (answer profile (history profile (r * (m * q) + i.val))) =
      favorite (profile i) (roundTypes profile r) hA := by
  have h := answer_type profile (r * (m * q) + i.val)
    (by simpa only [queryTypes_at_slot] using hA)
  simpa only [queryTypes_at_slot, history, queryAgent_at_slot] using h

lemma stochastic_nonempty (h : List (Fin (m * q)))
    (hs : stochasticRecording h = true) : (queryTypes h).Nonempty := by
  classical
  exact (of_decide_eq_true hs).1

def revealStep (profile : ReplicaPS.Profile m q) (depth : ℕ) : Option (Reveal m q) :=
  if hs : stochasticRecording (history profile depth) = true then
    some ⟨queryAgent (history profile depth), queryTypes (history profile depth),
      typeOf (answer profile (history profile depth)), by
        rw [answer_type profile depth (stochastic_nonempty _ hs)]
        exact favorite_mem _ _ _⟩
  else none

def revealHistory (profile : ReplicaPS.Profile m q) : ℕ → RevealHistory m q
  | 0 => []
  | depth + 1 => revealHistory profile depth ++ (revealStep profile depth).toList

@[simp] lemma revealHistory_zero (profile : ReplicaPS.Profile m q) :
    revealHistory profile 0 = [] := rfl

@[simp] lemma revealHistory_succ (profile : ReplicaPS.Profile m q) (depth : ℕ) :
    revealHistory profile (depth + 1) =
      revealHistory profile depth ++ (revealStep profile depth).toList := rfl

lemma revealStep_eq_some (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history profile depth) = true) :
    revealStep profile depth = some
      ⟨queryAgent (history profile depth), queryTypes (history profile depth),
        typeOf (answer profile (history profile depth)), by
          rw [answer_type profile depth (stochastic_nonempty _ hs)]
          exact favorite_mem _ _ _⟩ := by
  simp only [revealStep, dif_pos hs]

lemma revealStep_eq_none (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history profile depth) = false) :
    revealStep profile depth = none := by
  simp [revealStep, hs]

lemma mem_revealHistory (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (r : Reveal m q) :
    r ∈ revealHistory profile depth ↔
      ∃ k < depth,
        stochasticRecording (history profile k) = true ∧
        r.agent = queryAgent (history profile k) ∧
        r.available = queryTypes (history profile k) ∧
        r.chosen = typeOf (answer profile (history profile k)) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [revealHistory_succ, List.mem_append, ih]
      by_cases hs : stochasticRecording (history profile depth) = true
      · rw [revealStep_eq_some profile depth hs]
        simp only [Option.toList_some, List.mem_singleton]
        constructor
        · rintro (hold | rfl)
          · obtain ⟨k, hk, hstep, ha, hav, hc⟩ := hold
            exact ⟨k, by omega, hstep, ha, hav, hc⟩
          · exact ⟨depth, by omega, hs, rfl, rfl, rfl⟩
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          by_cases hkd : k < depth
          · exact Or.inl ⟨k, hkd, hstep, ha, hav, hc⟩
          · have hkeq : k = depth := by omega
            subst k
            right
            cases r
            simp_all
      · have hsFalse : stochasticRecording
            (history profile depth) = false := by
          exact Bool.eq_false_of_not_eq_true hs
        rw [revealStep_eq_none profile depth hsFalse]
        simp only [Option.toList_none, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          exact ⟨k, by omega, hstep, ha, hav, hc⟩
        · rintro ⟨k, hk, hstep, ha, hav, hc⟩
          refine ⟨k, ?_, hstep, ha, hav, hc⟩
          by_contra hnot
          have hkeq : k = depth := by omega
          subst k
          exact hs hstep



lemma revealHistory_mono (profile : ReplicaPS.Profile m q) {a b : ℕ} (hab : a ≤ b) :
    ∀ r ∈ revealHistory profile a, r ∈ revealHistory profile b := by
  intro r hr
  obtain ⟨k, hk, hs, ha, hA, hc⟩ := (mem_revealHistory profile a r).mp hr
  exact (mem_revealHistory profile b r).mpr ⟨k, lt_of_lt_of_le hk hab, hs, ha, hA, hc⟩

theorem revealHistory_compatible (profile : ReplicaPS.Profile m q) (depth : ℕ) :
    Compatible profile (revealHistory profile depth) := by
  intro r hr
  obtain ⟨k, hk, hs, ha, hA, hc⟩ := (mem_revealHistory profile depth r).mp hr
  have hf := answer_type profile k (stochastic_nonempty _ hs)
  calc
    favorite (profile r.agent) r.available r.nonempty =
        favorite (profile r.agent) (queryTypes (history profile k))
          (stochastic_nonempty _ hs) := favorite_congr_set _ _ _ _ _ hA
    _ = typeOf (answer profile (history profile k)) := by rw [ha]; exact hf.symm
    _ = r.chosen := hc.symm

theorem compatible_of_history_eq (reference other : ReplicaPS.Profile m q) (depth : ℕ)
    (heq : history reference depth = history other depth) :
    Compatible other (revealHistory reference depth) := by
  intro r hr
  obtain ⟨k, hk, hs, ha, hA, hc⟩ := (mem_revealHistory reference depth r).mp hr
  have hp : history reference k = history other k := profileHistory_prefix_eq heq hk.le
  have hn : history reference (k + 1) = history other (k + 1) :=
    profileHistory_prefix_eq heq (by omega)
  have hans : answer reference (history reference k) = answer other (history other k) := by
    have hh := congrArg List.head? hn
    simpa only [history, profileHistory_succ, List.head?_cons, Option.some.injEq] using hh
  have hAo : (queryTypes (history other k)).Nonempty := by
    rw [← hp]
    exact stochastic_nonempty _ hs
  calc
    favorite (other r.agent) r.available r.nonempty =
        favorite (other r.agent) (queryTypes (history other k)) hAo :=
      favorite_congr_set _ _ _ _ _ (hA.trans (congrArg queryTypes hp))
    _ = typeOf (answer other (history other k)) := by
      rw [ha, hp]
      exact (answer_type other k hAo).symm
    _ = r.chosen := (congrArg typeOf hans).symm.trans hc.symm

lemma depth_decomposition (profile : ReplicaPS.Profile m q) (depth : ℕ) :
    depth = (depth / (m * q)) * (m * q) + (queryAgent (history profile depth)).val := by
  simpa only [queryAgent, roundOffset, history, profileHistory_length, Nat.mul_comm,
    Nat.add_comm] using (Nat.mod_add_div depth (m * q)).symm

lemma answer_type_of_nonfresh (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hA : (queryTypes (history profile depth)).Nonempty)
    (hs : stochasticRecording (history profile depth) = false) :
    previousType (history profile depth) =
      some (typeOf (answer profile (history profile depth))) := by
  have hd := depth_decomposition profile depth
  let i := queryAgent (history profile depth)
  generalize hr : depth / (m * q) = r at hd
  change depth = r * (m * q) + i.val at hd
  have hAr : (roundTypes profile r).Nonempty := by
    rw [← queryTypes_at_slot profile r i, ← hd]
    exact hA
  cases r with
  | zero =>
      simp only [Nat.zero_mul, Nat.zero_add] at hd
      have hp : previousType (history profile depth) = none := by
        rw [hd]; exact previousType_at_slot_zero profile i
      have ht : stochasticRecording (history profile depth) = true := by
        simp only [stochasticRecording, FreshQuery, hp, and_true, decide_eq_true_eq]
        exact hA
      rw [hs] at ht
      contradiction
  | succ r =>
      have hp := previousType_at_slot_succ profile r i hAr
      rw [← hd] at hp
      have hkeep : favorite (profile i) (roundTypes profile r)
          (hAr.mono (roundTypes_subset profile (Nat.le_succ r))) ∈ roundTypes profile (r + 1) := by
        by_contra hnot
        have ht : stochasticRecording (history profile depth) = true := by
          simp only [stochasticRecording, FreshQuery, hp, decide_eq_true_eq]
          refine ⟨hA, ?_⟩
          simpa only [hd, queryTypes_at_slot] using hnot
        rw [hs] at ht
        contradiction
      rw [hp, hd, answer_type_at_slot profile (r + 1) i hAr]
      congr 1
      exact (ReplicaTrace.favorite_persists _ _ _
        (roundTypes_subset profile (Nat.le_succ r)) hkeep).symm

lemma answer_of_empty (profile : ReplicaPS.Profile m q) (depth : ℕ)
    (hA : ¬(queryTypes (history profile depth)).Nonempty) :
    answer profile (history profile depth) = defaultGood := by
  have hc : ¬(queryActive (history profile depth)).Nonempty :=
    fun h => hA (h.image typeOf)
  unfold answer profileAnswer queryAvailable
  simp only [dif_neg hc]
  exact PSRankIncrement.favorite_eq_of_rank_le _ _ _ (Finset.mem_singleton_self _)
    (by intro a ha; rw [Finset.mem_singleton.mp ha])

theorem history_eq_of_compatible (reference other : ReplicaPS.Profile m q) (depth : ℕ)
    (hc : Compatible other (revealHistory reference depth)) :
    history reference depth = history other depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      have hp := ih (fun r hr => hc r
        (revealHistory_mono reference (Nat.le_succ depth) r hr))
      have hans : answer reference (history reference depth) = answer other (history other depth) := by
        by_cases hA : (queryTypes (history reference depth)).Nonempty
        · have hAo : (queryTypes (history other depth)).Nonempty := by rwa [← hp]
          have ht : typeOf (answer reference (history reference depth)) =
              typeOf (answer other (history other depth)) := by
            by_cases hs : stochasticRecording (history reference depth) = true
            · let r : Reveal m q := ⟨queryAgent (history reference depth),
                queryTypes (history reference depth), typeOf (answer reference (history reference depth)),
                by rw [answer_type reference depth hA]; exact favorite_mem _ _ _⟩
              have hr : r ∈ revealHistory reference (depth + 1) := by
                rw [revealHistory_succ, revealStep_eq_some reference depth hs]
                exact List.mem_append_right _ (by simp [r])
              have hf := hc r hr
              change favorite (other (queryAgent (history reference depth)))
                (queryTypes (history reference depth)) _ =
                typeOf (answer reference (history reference depth)) at hf
              exact hf.symm.trans (by
                simpa only [hp] using (answer_type other depth hAo).symm)
            · have hs' := Bool.eq_false_of_not_eq_true hs
              have h1 := answer_type_of_nonfresh reference depth hA hs'
              have h2 := answer_type_of_nonfresh other depth hAo (by rwa [← hp])
              exact Option.some.inj (h1.symm.trans ((congrArg previousType hp).trans h2))
          rw [answer_eq_representative reference depth hA,
            answer_eq_representative other depth hAo, ht, hp]
        · rw [answer_of_empty reference depth hA, answer_of_empty other depth (by rwa [← hp])]
      change answer reference (history reference depth) :: history reference depth =
        answer other (history other depth) :: history other depth
      rw [hans, hp]

def pathFiber (depth : ℕ) (h : List (Fin (m * q))) : Finset (ReplicaPS.Profile m q) :=
  (ReplicaPS.profileSample m q).filter (fun p => history p depth = h)

theorem pathFiber_eq_compatibleProfiles (reference : ReplicaPS.Profile m q) (depth : ℕ) :
    pathFiber depth (history reference depth) = compatibleProfiles (revealHistory reference depth) := by
  ext other
  simp only [pathFiber, Finset.mem_filter, mem_compatibleProfiles_iff]
  constructor
  · rintro ⟨_, heq⟩
    exact compatible_of_history_eq reference other depth heq.symm
  · intro hc
    exact ⟨by rw [profileSample_eq_univ]; exact Finset.mem_univ _,
      (history_eq_of_compatible reference other depth hc).symm⟩

end ProbabilisticSerial.ReplicaChoiceMachine
