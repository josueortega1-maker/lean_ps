import PSChoiceMachine
import WeightedArrival

/-! A predictable clock and a finite, padded phase schedule for concrete PS. -/

noncomputable section
set_option maxHeartbeats 4000000
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PSChoiceMachine
open UniformPermutation PSProcess AdaptiveCategorical

variable {n : ℕ} [Nonempty (Fin n)]

lemma market_pos : 0 < n := by
  simpa using (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))

lemma supply_zero_of_inactive {q : SupplyState n} (hq : ValidState q)
    (hA : ¬ (activeGoods q).Nonempty) : q = fun _ => 0 := by
  funext g
  have hnot : ¬ 0 < q g := fun h => hA ⟨g, mem_activeGoods_iff.mpr h⟩
  exact le_antisymm (le_of_not_gt hnot) (hq g)

lemma profileSupply_le (profile : Profile n) (r : ℕ) (g : Fin n) :
    profileSupply profile (r + 1) g ≤ profileSupply profile r g := by
  rw [profileSupply]
  split
  · exact stepState_le _ _ _ _
  · exact le_rfl

lemma profileSupply_le_one (profile : Profile n) (r : ℕ) (g : Fin n) :
    profileSupply profile r g ≤ 1 := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact (profileSupply_le profile r g).trans ih

lemma profileSupply_card_le (profile : Profile n) (r : ℕ) :
    (activeGoods (profileSupply profile r)).card ≤ n - r := by
  induction r with
  | zero => simp [profileSupply, activeGoods_initial]
  | succ r ih =>
      rw [profileSupply]
      split
      next hA =>
        have hlt := activeGoods_step_card_lt profile (profileSupply profile r) hA
        omega
      next hA =>
        rw [Finset.not_nonempty_iff_eq_empty.mp hA]
        simp

lemma profileSupply_terminal (profile : Profile n) :
    profileSupply profile n = fun _ => 0 := by
  apply supply_zero_of_inactive (profileSupply_valid profile n)
  have hc := profileSupply_card_le profile n
  have he : activeGoods (profileSupply profile n) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  simp [he]

def roundTime (profile : Profile n) (r : ℕ) : ℝ :=
  1 - totalSupply (profileSupply profile r) / n

def queryTime (history : History (Fin n)) : ℝ :=
  1 - totalSupply (querySupply history) / n

def roundDuration (profile : Profile n) (r : ℕ) : ℝ :=
  if hA : (activeGoods (profileSupply profile r)).Nonempty then
    nextDelay profile (profileSupply profile r) hA else 0

def roundChoice (profile : Profile n) (r : ℕ) (i : Fin n) : Fin n :=
  profileAnswer profile (profileHistory profile (r * n + i.val))

lemma roundChoice_eq (profile : Profile n) (r : ℕ) (i : Fin n)
    (hA : (activeGoods (profileSupply profile r)).Nonempty) :
    roundChoice profile r i = favorite (profile i) (activeGoods (profileSupply profile r)) hA :=
  profileAnswer_at_slot profile r i hA

lemma queryTime_at_slot (profile : Profile n) (r : ℕ) (i : Fin n) :
    queryTime (profileHistory profile (r * n + i.val)) = roundTime profile r := by
  simp [queryTime, roundTime, querySupply_at_slot]

lemma roundTime_zero (profile : Profile n) : roundTime profile 0 = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (market_pos (n := n)).ne'
  simp [roundTime, profileSupply, totalSupply_initial, hn]

lemma roundTime_terminal (profile : Profile n) : roundTime profile n = 1 := by
  simp [roundTime, profileSupply_terminal, totalSupply]

lemma roundTime_nonneg (profile : Profile n) (r : ℕ) : 0 ≤ roundTime profile r := by
  have hs : totalSupply (profileSupply profile r) ≤ n := by
    calc
      _ ≤ ∑ _g : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun g _ => profileSupply_le_one profile r g)
      _ = _ := by simp
  have hn : (0 : ℝ) < n := by exact_mod_cast (market_pos (n := n))
  exact sub_nonneg.mpr ((div_le_one hn).mpr hs)

lemma roundTime_le_one (profile : Profile n) (r : ℕ) : roundTime profile r ≤ 1 := by
  have hs : 0 ≤ totalSupply (profileSupply profile r) :=
    Finset.sum_nonneg (fun g _ => profileSupply_valid profile r g)
  exact sub_le_self _ (div_nonneg hs (Nat.cast_nonneg _))

lemma roundDuration_nonneg (profile : Profile n) (r : ℕ) :
    0 ≤ roundDuration profile r := by
  unfold roundDuration
  split
  · exact (nextDelay_pos _ _ _).le
  · exact le_rfl

lemma roundTime_succ (profile : Profile n) (r : ℕ) :
    roundTime profile (r + 1) = roundTime profile r + roundDuration profile r := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (market_pos (n := n)).ne'
  unfold roundTime roundDuration
  rw [profileSupply]
  split
  next hA =>
    rw [totalSupply_step]
    field_simp [hn]
    <;> ring
  next hA => simp

lemma roundTime_mono (profile : Profile n) : Monotone (roundTime profile) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [roundTime_succ]
  exact le_add_of_nonneg_right (roundDuration_nonneg profile r)

lemma roundTime_lt_one_iff (profile : Profile n) (r : ℕ) :
    roundTime profile r < 1 ↔ (activeGoods (profileSupply profile r)).Nonempty := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (market_pos (n := n))
  constructor
  · intro ht
    by_contra hA
    have hz := supply_zero_of_inactive (profileSupply_valid profile r) hA
    simp [roundTime, hz, totalSupply] at ht
  · rintro ⟨g, hg⟩
    have hs : 0 < totalSupply (profileSupply profile r) :=
      Finset.sum_pos' (fun a _ => profileSupply_valid profile r a)
        ⟨g, Finset.mem_univ _, mem_activeGoods_iff.mp hg⟩
    exact sub_lt_self _ (div_pos hs hn)

lemma roundSupply_step (profile : Profile n) (r : ℕ) (g : Fin n) :
    profileSupply profile (r + 1) g = profileSupply profile r g -
      roundDuration profile r * (choiceDemand (roundChoice profile r) g : ℝ) := by
  unfold roundDuration
  rw [profileSupply]
  split
  next hA =>
    have hc : roundChoice profile r =
        fun i => favorite (profile i) (activeGoods (profileSupply profile r)) hA := by
      funext i
      exact roundChoice_eq profile r i hA
    rw [hc, choiceDemand_eq_demand]
    rfl
  next hA => simp

lemma roundSupply_conservation (profile : Profile n) (r : ℕ) (g : Fin n) :
    profileSupply profile r g = 1 - ∑ k ∈ Finset.range r,
      roundDuration profile k * (choiceDemand (roundChoice profile k) g : ℝ) := by
  induction r with
  | zero => simp [profileSupply, initialState]
  | succ r ih => rw [roundSupply_step, ih, Finset.sum_range_succ]; ring

lemma sum_roundDuration (profile : Profile n) (r : ℕ) :
    ∑ k ∈ Finset.range r, roundDuration profile k = roundTime profile r := by
  induction r with
  | zero => simp [roundTime_zero]
  | succ r ih => rw [Finset.sum_range_succ, ih, roundTime_succ]

lemma weightedSuccesses_profileHistory (X : History (Fin n) → Fin n → Bool)
    (z : History (Fin n) → ℝ) (profile : Profile n) (depth : ℕ) :
    weightedSuccesses X z (profileHistory profile depth) =
      ∑ k ∈ Finset.range depth, z (profileHistory profile k) *
        (if X (profileHistory profile k)
          (profileAnswer profile (profileHistory profile k)) then 1 else 0) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [profileHistory_succ, weightedSuccesses, ih, Finset.sum_range_succ]

lemma weightedCompensator_profileHistory (X : History (Fin n) → Fin n → Bool)
    (z : History (Fin n) → ℝ) (θ : ℝ) (profile : Profile n) (depth : ℕ) :
    weightedCompensator machineWeight X z θ (profileHistory profile depth) =
      ∑ k ∈ Finset.range depth,
        successProbability machineWeight X (profileHistory profile k) *
          (1 - Real.exp (-θ * z (profileHistory profile k))) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [profileHistory_succ, weightedCompensator, ih, Finset.sum_range_succ]

/-- Discrete integration by parts with a zero terminal weight. -/
lemma weighted_entries_eq_integral (z a : ℕ → ℝ) (N : ℕ) (hz : z N = 0) :
    z 0 * a 0 + (∑ k ∈ Finset.range N, z (k + 1) * (a (k + 1) - a k)) =
      ∑ k ∈ Finset.range N, (z k - z (k + 1)) * a k := by
  have h : ∀ N : ℕ,
      z 0 * a 0 + (∑ k ∈ Finset.range N, z (k + 1) * (a (k + 1) - a k)) =
        (∑ k ∈ Finset.range N, (z k - z (k + 1)) * a k) + z N * a N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => simp only [Finset.sum_range_succ]; linear_combination ih
  simpa [hz] using h N

end ProbabilisticSerial.PSChoiceMachine
