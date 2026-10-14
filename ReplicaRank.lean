import ReplicaPS

/-!+# Replica static concentration and the actual dynamic rank

The concentration law is for `m*q` independent permutations of `m` types.
The dynamic identity uses the verified eating run with grouped copies.
No uniform distribution on permutations of the copies is asserted.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRank

open UniformPermutation UniformProduct PSProcess ReplicaPS

theorem uniform_active_rank {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {K c : ℝ}
    (hK : Real.log 2 + c ≤ (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1)) :
    probability (ReplicaPS.profileSample m q)
      (fun profile => ∃ S ∈ nonemptyActiveSets m,
        K * (m * q : ℕ) ≤ ∑ i : Fin (m * q), scaledActiveRank m S (profile i)) ≤
      Real.exp (-c * (m * q : ℕ)) := by
  apply uniform_active_rank_exponential (preferenceSample m) (nonemptyActiveSets m)
    (scaledActiveRank m)
  · intro S hS
    exact activeRank_scaled_mgf hm (mem_nonemptyActiveSets_iff.mp hS)
  · exact hK
  · exact (card_nonemptyActiveSets_le m).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2)
        (by simpa using Nat.mul_le_mul_left m hq))

def UniformRankGood {m q : ℕ} (profile : ReplicaPS.Profile m q) (K : ℝ) : Prop :=
  ∀ S : Finset (Fin m), S.Nonempty →
    (∑ i : Fin (m * q), scaledActiveRank m S (profile i)) < K * (m * q : ℕ)

noncomputable instance {m q : ℕ} (profile : ReplicaPS.Profile m q) (K : ℝ) :
    Decidable (UniformRankGood profile K) := Classical.propDecidable _

theorem uniformRankGood_failure_probability {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {K c : ℝ}
    (hK : Real.log 2 + c ≤ (1 / 2 : ℝ) * K - Real.log (1 + Real.exp 1)) :
    probability (ReplicaPS.profileSample m q) (fun profile => ¬UniformRankGood profile K) ≤
      Real.exp (-c * (m * q : ℕ)) := by
  have heq (profile : ReplicaPS.Profile m q) :
      (¬UniformRankGood profile K) ↔ ∃ S ∈ nonemptyActiveSets m,
        K * (m * q : ℕ) ≤ ∑ i : Fin (m * q), scaledActiveRank m S (profile i) := by
    simp only [UniformRankGood, not_forall, not_lt, mem_nonemptyActiveSets_iff]
    simp
  simpa only [heq] using uniform_active_rank hm hq hK

abbrev ReplicaPhase {m q : ℕ} (profile : ReplicaPS.Profile m q) :=
  Phase (m * q) (liftedProfile profile)

def activeTypes {m q : ℕ} {profile : ReplicaPS.Profile m q} (p : ReplicaPhase profile) :
    Finset (Fin m) := p.active.image typeOf

lemma activeTypes_nonempty {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) : (activeTypes p).Nonempty := p.active_nonempty.image typeOf

lemma rank_choice_type {m q : ℕ} {profile : ReplicaPS.Profile m q}
    (p : ReplicaPhase profile) (i : Fin (m * q)) :
    rankOf (profile i) (typeOf (p.choice i)) = activeRank (activeTypes p) (profile i) := by
  change rankOf (profile i)
    (typeOf (favorite (liftPreference (profile i)) p.active p.active_nonempty)) = _
  rw [favorite_type]
  exact rankOf_favorite_eq_activeRank (profile i) _ _

lemma weighted_allocationFrom {n : ℕ} {profile : PSProcess.Profile n}
    (phases : List (Phase n profile)) (w : Fin n → ℝ) (i : Fin n) :
    (∑ g, w g * allocationFrom phases i g) =
      (phases.map (fun p => p.duration * w (p.choice i))).sum := by
  induction phases with
  | nil => simp [allocationFrom]
  | cons p phases ih =>
      simp only [allocationFrom, List.map_cons, List.sum_cons, mul_add,
        Finset.sum_add_distrib] at ih ⊢
      rw [ih]
      simp only [mul_ite, mul_zero]
      simp [mul_comm]

theorem agentRank_eq_phase_sum {m q : ℕ} (profile : ReplicaPS.Profile m q)
    (i : Fin (m * q)) :
    agentRank profile i = ((run (liftedProfile profile)).phases.map
      (fun p => p.duration * (activeRank (activeTypes p) (profile i) : ℝ))).sum := by
  have hc := sum_copies (fun c => (rankOf (profile i) (typeOf c) : ℝ) *
    PSProcess.allocation (run (liftedProfile profile)) i c)
  simp only [typeOf_copyOf] at hc
  unfold agentRank ReplicaPS.allocation
  simp_rw [Finset.mul_sum]
  rw [hc]
  unfold PSProcess.allocation
  rw [weighted_allocationFrom]
  simp_rw [rank_choice_type]

def phaseRank {m q : ℕ} {profile : ReplicaPS.Profile m q} (p : ReplicaPhase profile) : ℝ :=
  𝔼 i : Fin (m * q), (activeRank (activeTypes p) (profile i) : ℝ)

def eatingIntegral {m q : ℕ} (profile : ReplicaPS.Profile m q) : ℝ :=
  ((run (liftedProfile profile)).phases.map
    (fun p => p.duration * ((m : ℝ) / (activeTypes p).card))).sum

theorem averageRank_eq_phase_sum {m q : ℕ} (profile : ReplicaPS.Profile m q) :
    ReplicaPS.averageRank profile = ((run (liftedProfile profile)).phases.map
      (fun p => p.duration * phaseRank p)).sum := by
  unfold ReplicaPS.averageRank
  simp_rw [agentRank_eq_phase_sum]
  induction (run (liftedProfile profile)).phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.expect_add_distrib, ih, ← Finset.mul_expect]
      rfl

lemma phaseRank_le {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {profile : ReplicaPS.Profile m q} {K : ℝ} (hgood : UniformRankGood profile K)
    (p : ReplicaPhase profile) : phaseRank p ≤ K * ((m : ℝ) / (activeTypes p).card) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (m * q : ℕ) := by exact_mod_cast Nat.mul_pos hm hq
  have hsR : (0 : ℝ) < (activeTypes p).card := by
    exact_mod_cast Finset.card_pos.mpr (activeTypes_nonempty p)
  have h := (hgood (activeTypes p) (activeTypes_nonempty p)).le
  simp only [scaledActiveRank] at h
  rw [← Finset.mul_sum, div_mul_eq_mul_div] at h
  have hprod := (div_le_iff₀ hmR).mp h
  unfold phaseRank
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hnR hsR).2
  nlinarith [hprod]

/-- The actual replica rank is reduced to its type-level eating integral. -/
theorem run_rankReduction {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (profile : ReplicaPS.Profile m q) {K : ℝ} (hgood : UniformRankGood profile K) :
    ReplicaPS.averageRank profile ≤ K * eatingIntegral profile := by
  rw [averageRank_eq_phase_sum]
  unfold eatingIntegral
  induction (run (liftedProfile profile)).phases with
  | nil => simp
  | cons p phases ih =>
      simp only [List.map_cons, List.sum_cons]
      have h := mul_le_mul_of_nonneg_left (phaseRank_le hm hq hgood p) p.duration_pos.le
      nlinarith [h]

end ProbabilisticSerial.ReplicaRank
