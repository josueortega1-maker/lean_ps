import PSFiniteClock

/-! Partial-time capacity identities for the actual finite PS schedule. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess
variable {n : ℕ} [Nonempty (Fin n)]

lemma ramp_difference (a b t : ℝ) (hab : a ≤ b) :
    max (t - a) 0 - max (t - b) 0 = min (b - a) (max (t - a) 0) := by
  by_cases hta : t ≤ a
  · rw [max_eq_right (by linarith : t - a ≤ 0),
      max_eq_right (by linarith : t - b ≤ 0), min_eq_right (by linarith)]
    ring
  · by_cases htb : t ≤ b
    · rw [max_eq_left (by linarith : 0 ≤ t - a),
        max_eq_right (by linarith : t - b ≤ 0), min_eq_right (by linarith)]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ t - a),
        max_eq_left (by linarith : 0 ≤ t - b), min_eq_left (by linarith)]
      ring

def partialDuration (profile : Profile n) (t : ℝ) (r : ℕ) : ℝ :=
  min (roundDuration profile r) (max (t - roundTime profile r) 0)

lemma partialDuration_eq_ramp (profile : Profile n) (t : ℝ) (r : ℕ) :
    partialDuration profile t r = max (t - roundTime profile r) 0 -
      max (t - roundTime profile (r + 1)) 0 := by
  rw [ramp_difference _ _ _ (roundTime_mono profile (Nat.le_succ r)), roundTime_succ]
  simp [partialDuration]

lemma partialDuration_nonneg (profile : Profile n) (t : ℝ) (r : ℕ) :
    0 ≤ partialDuration profile t r :=
  le_min (roundDuration_nonneg profile r) (le_max_right _ _)

lemma partialDuration_le_duration (profile : Profile n) (t : ℝ) (r : ℕ) :
    partialDuration profile t r ≤ roundDuration profile r := min_le_left _ _

lemma partialDuration_mono (profile : Profile n) (r : ℕ) :
    Monotone (fun t => partialDuration profile t r) := by
  intro s t hst
  exact min_le_min_left _ (max_le_max_right _ (sub_le_sub_right hst _))

lemma partialDuration_eq_zero (profile : Profile n) {t : ℝ} (r : ℕ)
    (ht : t ≤ roundTime profile r) : partialDuration profile t r = 0 := by
  unfold partialDuration
  rw [max_eq_right (sub_nonpos.mpr ht), min_eq_right (roundDuration_nonneg profile r)]

lemma partialDuration_eq_full (profile : Profile n) {t : ℝ} (r : ℕ)
    (ht : roundTime profile (r + 1) ≤ t) :
    partialDuration profile t r = roundDuration profile r := by
  apply min_eq_left
  apply le_trans _ (le_max_left _ _)
  rw [roundTime_succ] at ht
  linarith

lemma sum_partialDuration (profile : Profile n) (t : ℝ) (r : ℕ) :
    ∑ k ∈ Finset.range r, partialDuration profile t k =
      max t 0 - max (t - roundTime profile r) 0 := by
  induction r with
  | zero => simp [roundTime_zero]
  | succ r ih =>
      rw [Finset.sum_range_succ, ih, partialDuration_eq_ramp]
      ring

lemma sum_partialDuration_terminal (profile : Profile n) (t : ℝ) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) : ∑ k ∈ Finset.range n, partialDuration profile t k = t := by
  rw [sum_partialDuration, roundTime_terminal, max_eq_left ht,
    max_eq_right (sub_nonpos.mpr ht1), sub_zero]

lemma sum_choiceDemand (choice : Fin n → Fin n) :
    ∑ g : Fin n, (choiceDemand choice g : ℝ) = n := by
  simp only [choiceDemand, choiceConsumers, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  simp

def partialConsumption (profile : Profile n) (t : ℝ) (g : Fin n) : ℝ :=
  ∑ k ∈ Finset.range n,
    partialDuration profile t k * (choiceDemand (roundChoice profile k) g : ℝ)

def residual (profile : Profile n) (t : ℝ) (g : Fin n) : ℝ :=
  1 - partialConsumption profile t g

lemma partialConsumption_nonneg (profile : Profile n) (t : ℝ) (g : Fin n) :
    0 ≤ partialConsumption profile t g :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (partialDuration_nonneg _ _ _) (Nat.cast_nonneg _))

lemma partialConsumption_le_one (profile : Profile n) (t : ℝ) (g : Fin n) :
    partialConsumption profile t g ≤ 1 := by
  have h := roundSupply_conservation profile n g
  rw [profileSupply_terminal] at h
  dsimp only at h
  have hs : partialConsumption profile t g ≤
      ∑ k ∈ Finset.range n,
        roundDuration profile k * (choiceDemand (roundChoice profile k) g : ℝ) :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (partialDuration_le_duration _ _ _) (Nat.cast_nonneg _))
  linarith

lemma partialConsumption_mono (profile : Profile n) (g : Fin n) :
    Monotone (fun t => partialConsumption profile t g) := by
  intro s t hst
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (partialDuration_mono profile k hst) (Nat.cast_nonneg _))

lemma residual_nonneg (profile : Profile n) (t : ℝ) (g : Fin n) :
    0 ≤ residual profile t g := sub_nonneg.mpr (partialConsumption_le_one _ _ _)

lemma residual_le_one (profile : Profile n) (t : ℝ) (g : Fin n) :
    residual profile t g ≤ 1 := sub_le_self _ (partialConsumption_nonneg _ _ _)

lemma residual_antitone (profile : Profile n) (g : Fin n) :
    Antitone (fun t => residual profile t g) := by
  intro s t hst
  exact sub_le_sub_left (partialConsumption_mono profile g hst) _

lemma sum_residual (profile : Profile n) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ g : Fin n, residual profile t g = n * (1 - t) := by
  simp only [residual, partialConsumption, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_choiceDemand]
  rw [← Finset.sum_mul, sum_partialDuration_terminal profile t ht ht1]
  simp
  <;> ring

lemma residual_at_roundTime (profile : Profile n) (r : ℕ) (hr : r ≤ n) (g : Fin n) :
    residual profile (roundTime profile r) g = profileSupply profile r g := by
  rw [residual, partialConsumption, roundSupply_conservation]
  congr 1
  have hsmall : (∑ k ∈ Finset.range r,
      partialDuration profile (roundTime profile r) k *
        (choiceDemand (roundChoice profile k) g : ℝ)) =
      ∑ k ∈ Finset.range r,
        roundDuration profile k * (choiceDemand (roundChoice profile k) g : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [partialDuration_eq_full profile k
      (roundTime_mono profile (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))]
  rw [← hsmall]
  symm
  apply Finset.sum_subset (Finset.range_mono hr)
  intro k hkn hkr
  rw [partialDuration_eq_zero profile k (roundTime_mono profile
    (by simpa only [Finset.mem_range, not_lt] using hkr)), zero_mul]

lemma residual_pos_implies_active (profile : Profile n) (t : ℝ) (g : Fin n)
    (hg : 0 < residual profile t g) (r : ℕ) (hr : r ≤ n)
    (ht : roundTime profile r ≤ t) : g ∈ activeGoods (profileSupply profile r) := by
  apply mem_activeGoods_iff.mpr
  rw [← residual_at_roundTime profile r hr g]
  exact hg.trans_le (residual_antitone profile g ht)

/-- A good in the final nonempty phase survives every strictly earlier query. -/
lemma exists_last_survivor (profile : Profile n) :
    ∃ g : Fin n, ∀ r : ℕ, roundTime profile r < 1 →
      g ∈ activeGoods (profileSupply profile r) := by
  classical
  have hex : ∃ r, ¬ (activeGoods (profileSupply profile r)).Nonempty := by
    refine ⟨n, ?_⟩
    simp [profileSupply_terminal, activeGoods]
  let stop := Nat.find hex
  have hstop : ¬ (activeGoods (profileSupply profile stop)).Nonempty := Nat.find_spec hex
  have hpos : 0 < stop := by
    by_contra hz
    have he : stop = 0 := by omega
    have hinit : (activeGoods (profileSupply profile 0)).Nonempty := by
      simpa [profileSupply, activeGoods_initial] using (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin n)).Nonempty)
    exact hstop (he ▸ hinit)
  have hprev : (activeGoods (profileSupply profile (stop - 1))).Nonempty := by
    by_contra h
    have := Nat.find_min' hex h
    change stop ≤ stop - 1 at this
    omega
  refine ⟨hprev.choose, ?_⟩
  intro r hr
  have hactive := (roundTime_lt_one_iff profile r).mp hr
  have hrs : r < stop := by
    by_contra h
    have hsub := profileSupply_active_subset_of_le profile (Nat.le_of_not_gt h)
    exact hstop ⟨hactive.choose, hsub hactive.choose_spec⟩
  exact profileSupply_active_subset_of_le profile (by omega : r ≤ stop - 1) hprev.choose_spec

end ProbabilisticSerial.PSChoiceMachine
