import ReplicaRank
import UniformLowerRank

/-!
# Lower-rank estimates on the actual replica PS run

This file proves static concentration and the pathwise rank reduction on a
specified range of active-set sizes. The growth of the eating integral is a
separate obligation; these results do not assert the fixed-quota asymptotic.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaLowerRank
open UniformProduct UniformPermutation ReplicaPS ReplicaRank PSProcess

def activeSizeBand (m lo hi : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ lo ≤ S.card ∧ S.card ≤ hi)

@[simp] lemma mem_activeSizeBand {m lo hi : ℕ} (S : Finset (Fin m)) :
    S ∈ activeSizeBand m lo hi ↔ S.Nonempty ∧ lo ≤ S.card ∧ S.card ≤ hi := by
  simp [activeSizeBand]

def UniformLowerRankGood {m q : ℕ} (profile : ReplicaPS.Profile m q)
    (K : ℝ) (lo hi : ℕ) : Prop :=
  ∀ S ∈ activeSizeBand m lo hi,
    K * (m * q : ℕ) ≤ ∑ i : Fin (m * q), scaledActiveRank m S (profile i)

noncomputable instance {m q : ℕ} (profile : ReplicaPS.Profile m q)
    (K : ℝ) (lo hi : ℕ) : Decidable (UniformLowerRankGood profile K lo hi) :=
  Classical.propDecidable _

theorem uniformLowerRankGood_failure_probability {m q lo hi : ℕ} (hm : 0 < m)
    {θ a K : ℝ} (hθ : 0 < θ) (ha : a ≤ 1 - 1 / (lo + 1 : ℝ)) :
    probability (ReplicaPS.profileSample m q)
      (fun profile => ¬UniformLowerRankGood profile K lo hi) ≤
      ((activeSizeBand m lo hi).card : ℝ) *
        Real.exp (-(m * q : ℕ) * (θ * (a - K) - θ ^ 2 * (16 * (1 + Real.exp 1)))) := by
  classical
  calc
    _ ≤ probability (ReplicaPS.profileSample m q)
        (fun profile => ∃ S ∈ activeSizeBand m lo hi,
          (∑ i : Fin (m * q), scaledActiveRank m S (profile i)) ≤ K * (m * q : ℕ)) := by
      apply probability_mono
      intro profile hp hbad
      simp only [UniformLowerRankGood, not_forall, not_le] at hbad
      obtain ⟨S, hS, hlt⟩ := hbad
      exact ⟨S, hS, hlt.le⟩
    _ ≤ ∑ S ∈ activeSizeBand m lo hi, probability (ReplicaPS.profileSample m q)
        (fun profile => (∑ i : Fin (m * q), scaledActiveRank m S (profile i)) ≤
          K * (m * q : ℕ)) := union_bound _ _ _
    _ ≤ ∑ _S ∈ activeSizeBand m lo hi,
        Real.exp (-(m * q : ℕ) * (θ * (a - K) - θ ^ 2 * (16 * (1 + Real.exp 1)))) := by
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨hs, hlo, hhi⟩ := (mem_activeSizeBand S).1 hS
      apply UniformLowerRank.fixed_set_lower_tail hm hs hθ
      have hloR : (lo : ℝ) ≤ S.card := by exact_mod_cast hlo
      have hinv : 1 / (S.card + 1 : ℝ) ≤ 1 / (lo + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    _ = _ := by simp

def bandEatingIntegral {m q : ℕ} (profile : ReplicaPS.Profile m q) (lo hi : ℕ) : ℝ :=
  ((run (liftedProfile profile)).phases.map (fun p =>
    if activeTypes p ∈ activeSizeBand m lo hi then
      p.duration * ((m : ℝ) / (activeTypes p).card) else 0)).sum

lemma phaseRank_nonneg {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) : 0 ≤ phaseRank p := by
  apply Finset.expect_nonneg
  intro i hi
  exact Nat.cast_nonneg _

theorem phaseRank_lower {m q lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    {profile : ReplicaPS.Profile m q} {K : ℝ}
    (hgood : UniformLowerRankGood profile K lo hi)
    (p : ReplicaPhase profile) (hp : activeTypes p ∈ activeSizeBand m lo hi) :
    K * ((m : ℝ) / (activeTypes p).card) ≤ phaseRank p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (m * q : ℕ) := by exact_mod_cast Nat.mul_pos hm hq
  have hsR : (0 : ℝ) < (activeTypes p).card := by
    exact_mod_cast Finset.card_pos.mpr (activeTypes_nonempty p)
  have h := hgood (activeTypes p) hp
  simp only [scaledActiveRank] at h
  rw [← Finset.mul_sum, div_mul_eq_mul_div] at h
  have hprod := (le_div_iff₀ hmR).mp h
  unfold phaseRank
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hsR hnR).2
  nlinarith

theorem meanRank_lower {m q lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    {profile : ReplicaPS.Profile m q} {K : ℝ}
    (hgood : UniformLowerRankGood profile K lo hi)
    (S : Finset (Fin m)) (hS : S ∈ activeSizeBand m lo hi) :
    K * ((m : ℝ) / S.card) ≤
      𝔼 i : Fin (m * q), (activeRank S (profile i) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (m * q : ℕ) := by exact_mod_cast Nat.mul_pos hm hq
  have hsR : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ((mem_activeSizeBand S).1 hS).1
  have h := hgood S hS
  simp only [scaledActiveRank] at h
  rw [← Finset.mul_sum, div_mul_eq_mul_div] at h
  have hprod := (le_div_iff₀ hmR).mp h
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hsR hnR).2
  nlinarith

lemma activeRank_antitone {m : ℕ} (S T : Finset (Fin m))
    (hS : S.Nonempty) (hST : S ⊆ T) (σ : PreferenceOrder m) :
    activeRank T σ ≤ activeRank S σ := by
  have hT := hS.mono hST
  rw [← rankOf_favorite_eq_activeRank σ T hT, ← rankOf_favorite_eq_activeRank σ S hS]
  exact favorite_rank_le σ T hT _ (hST (favorite_mem σ S hS))

/-- A good estimate at the cutoff also controls smaller active sets:
enlarging the available set can only improve its best rank. -/
theorem meanRank_lower_with_cutoff {m q lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hlm : lo ≤ m) (hlh : lo ≤ hi)
    {profile : ReplicaPS.Profile m q} {K : ℝ}
    (hgood : UniformLowerRankGood profile K lo hi)
    (S : Finset (Fin m)) (hS : S.Nonempty) (hShi : S.card ≤ hi) :
    K * ((m : ℝ) / (max lo S.card : ℕ)) ≤
      𝔼 i : Fin (m * q), (activeRank S (profile i) : ℝ) := by
  by_cases hlarge : lo ≤ S.card
  · rw [max_eq_right hlarge]
    exact meanRank_lower hm hq hgood S ((mem_activeSizeBand S).2 ⟨hS, hlarge, hShi⟩)
  · have hsmall : S.card ≤ lo := le_of_not_ge hlarge
    obtain ⟨T, hST, hTcard⟩ := Finset.exists_superset_card_eq hsmall (by simpa using hlm)
    rw [max_eq_left hsmall]
    have hT : T ∈ activeSizeBand m lo hi :=
      (mem_activeSizeBand T).2 ⟨hS.mono hST, by omega, by omega⟩
    have h := meanRank_lower hm hq hgood T hT
    rw [hTcard] at h
    apply h.trans
    exact Finset.expect_le_expect (fun i _ => by
      exact_mod_cast activeRank_antitone S T hS hST (profile i))

theorem run_rank_lower_reduction {m q lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    (profile : ReplicaPS.Profile m q) {K : ℝ}
    (hgood : UniformLowerRankGood profile K lo hi) :
    K * bandEatingIntegral profile lo hi ≤ ReplicaPS.averageRank profile := by
  rw [averageRank_eq_phase_sum]
  unfold bandEatingIntegral
  induction (run (liftedProfile profile)).phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons]
      by_cases hp : activeTypes p ∈ activeSizeBand m lo hi
      · rw [if_pos hp]
        have h := mul_le_mul_of_nonneg_left (phaseRank_lower hm hq hgood p hp)
          p.duration_pos.le
        nlinarith
      · rw [if_neg hp, zero_add]
        have h := mul_nonneg p.duration_pos.le (phaseRank_nonneg p)
        linarith

theorem bandEatingIntegral_nonneg {m q : ℕ} (profile : ReplicaPS.Profile m q)
    (lo hi : ℕ) : 0 ≤ bandEatingIntegral profile lo hi := by
  unfold bandEatingIntegral
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact mul_nonneg p.duration_pos.le (by positivity)
  · rfl

theorem bandEatingIntegral_le_market {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (profile : ReplicaPS.Profile m q) (lo hi : ℕ) :
    bandEatingIntegral profile lo hi ≤ m := by
  have hterm (p : ReplicaPhase profile) :
      (if activeTypes p ∈ activeSizeBand m lo hi then
        p.duration * ((m : ℝ) / (activeTypes p).card) else 0) ≤ p.duration * m := by
    split_ifs
    · apply mul_le_mul_of_nonneg_left _ p.duration_pos.le
      have hcard : (1 : ℝ) ≤ (activeTypes p).card := by
        exact_mod_cast Finset.card_pos.mpr (activeTypes_nonempty p)
      exact div_le_self (Nat.cast_nonneg m) hcard
    · exact mul_nonneg p.duration_pos.le (Nat.cast_nonneg m)
  have hsum (phases : List (ReplicaPhase profile)) :
      (phases.map (fun p => if activeTypes p ∈ activeSizeBand m lo hi then
        p.duration * ((m : ℝ) / (activeTypes p).card) else 0)).sum ≤
      (phases.map Phase.duration).sum * m := by
    induction phases with
    | nil => simp
    | cons p phases ih =>
        simp only [List.map_cons, List.sum_cons]
        nlinarith [hterm p]
  have h := hsum (run (liftedProfile profile)).phases
  change bandEatingIntegral profile lo hi ≤ totalDuration (run (liftedProfile profile)) * m at h
  simpa only [run_totalDuration _ (Nat.mul_pos hm hq), one_mul] using h

/-- Averaging the pathwise bound does not assume independence of the good
event and the endogenous phase integral. -/
theorem expectedPS_ge_band_sub_failure {m q lo hi : ℕ} (hm : 0 < m) (hq : 0 < q)
    {K : ℝ} (hK : 0 ≤ K) :
    K * (𝔼 profile ∈ ReplicaPS.profileSample m q, bandEatingIntegral profile lo hi) -
      K * m * probability (ReplicaPS.profileSample m q)
        (fun profile => ¬UniformLowerRankGood profile K lo hi) ≤ ReplicaPS.expectedPS m q := by
  have h := expect_mono (ReplicaPS.profileSample m q)
    (f := fun profile => K * bandEatingIntegral profile lo hi -
      K * m * (if ¬UniformLowerRankGood profile K lo hi then (1 : ℝ) else 0))
    (g := ReplicaPS.averageRank)
    (by
      intro profile hp
      by_cases hg : UniformLowerRankGood profile K lo hi
      · simpa only [not_true_eq_false, hg, if_false, mul_zero, sub_zero] using
          run_rank_lower_reduction hm hq profile hg
      · simp only [hg, not_false_eq_true, if_true, mul_one]
        have hb := mul_le_mul_of_nonneg_left
          (bandEatingIntegral_le_market hm hq profile lo hi) hK
        have hr := (ReplicaPS.averageRank_bounds profile hm hq).1
        linarith)
  simpa only [Finset.expect_sub_distrib, ← Finset.mul_expect,
    probability, ReplicaPS.expectedPS] using h

end ProbabilisticSerial.ReplicaLowerRank
