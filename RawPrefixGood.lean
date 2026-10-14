import RawSurvivorBound
import ReplicaRawRankBridge

/-! Simultaneous raw-prefix count estimates, including the last draw in a phase. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.RawPrefixGood
open UniformProduct CouponLowerBound UniformRawPrefixes ReplicaPS ReplicaChoiceMachine
  ReplicaRawStep ReplicaRawProcess ReplicaRawRankBridge

def CountsGood {m N : ℕ} (w : Fin N → Fin m)
    (family : Finset (Finset (Fin m))) (α n : ℝ) : Prop :=
  ∀ k : Fin (N + 1), ∀ S ∈ family,
    α * n ≤ k.val * ((S.card : ℝ) / m) →
      n < RawSubsetCounts.count S (rawPrefix k.val (by omega) w)

noncomputable instance {m N : ℕ} (w : Fin N → Fin m)
    (family : Finset (Finset (Fin m))) (α n : ℝ) : Decidable (CountsGood w family α n) :=
  Classical.propDecidable _

theorem CountsGood.tail {m N : ℕ} {w : Fin (N + 1) → Fin m}
    {family : Finset (Finset (Fin m))} {α n : ℝ}
    (h : CountsGood w family α n) : CountsGood (Fin.tail w) family α n := by
  intro k S hS hmean
  have hk : k.val ≤ N := by omega
  have hh := h k.castSucc S hS hmean
  simpa only [Fin.coe_castSucc, ← rawPrefix_tail hk w] using hh

theorem CountsGood.full {m N : ℕ} {w : Fin N → Fin m}
    {family : Finset (Finset (Fin m))} {α n : ℝ}
    (h : CountsGood w family α n) (S : Finset (Fin m)) (hS : S ∈ family)
    (hmean : α * n ≤ N * ((S.card : ℝ) / m)) : n < RawSubsetCounts.count S w := by
  simpa only [Fin.val_last, rawPrefix_self] using h (Fin.last N) S hS hmean

theorem countsGood_failure_probability {m N : ℕ} (hm : 0 < m)
    (family : Finset (Finset (Fin m))) {α n : ℝ} (hα : 1 < α) :
    probability (labelSample m N) (fun w => ¬ CountsGood w family α n) ≤
      (N + 1 : ℕ) * (family.card : ℝ) * Real.exp (-(α - 1 - Real.log α) * n) := by
  classical
  let bad (k : Fin (N + 1)) (S : Finset (Fin m)) (w : Fin N → Fin m) : Prop :=
    α * n ≤ k.val * ((S.card : ℝ) / m) ∧
      RawSubsetCounts.count S (rawPrefix k.val (by omega) w) ≤ n
  have hsub : probability (labelSample m N) (fun w => ¬CountsGood w family α n) ≤
      probability (labelSample m N) (fun w => ∃ k : Fin (N + 1), ∃ S ∈ family, bad k S w) := by
    apply probability_mono
    intro w hw hbad
    simp only [CountsGood, not_forall, not_lt] at hbad
    obtain ⟨k, S, hS, hmean, hbad⟩ := hbad
    exact ⟨k, S, hS, hmean, hbad⟩
  apply hsub.trans
  have hu := union_bound (labelSample m N) (Finset.univ : Finset (Fin (N + 1)))
    (fun k w => ∃ S ∈ family, bad k S w)
  simp only [Finset.mem_univ, true_and] at hu
  apply hu.trans
  calc
    _ ≤ ∑ k : Fin (N + 1), ∑ S ∈ family, probability (labelSample m N) (bad k S) :=
      Finset.sum_le_sum (fun k _ => union_bound _ family (bad k))
    _ ≤ ∑ _k : Fin (N + 1), ∑ _S ∈ family,
        Real.exp (-(α - 1 - Real.log α) * n) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro S hS
      by_cases hmean : α * n ≤ k.val * ((S.card : ℝ) / m)
      · have heq : probability (labelSample m N) (bad k S) =
            probability (labelSample m k.val) (fun v => RawSubsetCounts.count S v ≤ n) := by
          simp only [bad, hmean, true_and]
          exact probability_prefix (m := m) (N := N) (k := k.val) hm (by omega)
            (fun v => RawSubsetCounts.count S v ≤ n)
        rw [heq]
        exact RawSubsetCounts.count_lower_tail_of_mean_ge hm S k.val hα hmean
      · have hz : probability (labelSample m N) (bad k S) = 0 := by
          simp [probability, bad, hmean]
        rw [hz]
        exact (Real.exp_pos _).le
    _ = _ := by simp [mul_assoc]

variable {m q : ℕ} [Nonempty (Fin (m * q))]

theorem rawRoundCount_bound (hm : 0 < m) (reference : ReplicaPS.Profile m q)
    (N : ℕ) (w : Fin N → Fin m) (p : ReplicaPS.Profile m q)
    (hp : p ∈ fiber ((initialState reference).evolve N w).reference
      ((initialState reference).evolve N w).depth)
    (family : Finset (Finset (Fin m))) {α : ℝ} (hα : 0 ≤ α)
    (hgood : CountsGood w family α (m * q : ℕ))
    (r : ℕ) (hS : roundTypes p r ∈ family) (hne : (roundTypes p r).Nonempty) :
    (rawRoundCount (initialState reference) r N w : ℝ) / m ≤
      α * (m * q : ℕ) / (roundTypes p r).card := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcard : (0 : ℝ) < (roundTypes p r).card := by exact_mod_cast Finset.card_pos.mpr hne
  induction N with
  | zero => simp only [rawRoundCount, Nat.cast_zero, zero_div]; positivity
  | succ N ih =>
      let s := (initialState reference).evolve N (Fin.tail w)
      have hp' : p ∈ fiber s.reference s.depth := s.step_fiber_subset (w 0) hp
      by_cases hround : s.normalize.depth / (m * q) ≤ r
      · have hpn : p ∈ fiber s.normalize.reference s.normalize.depth := by
          rwa [State.normalize_fiber]
        have hsub : roundTypes p r ⊆ s.normalize.active := by
          rw [s.normalize.active_on_fiber p hpn]
          exact roundTypes_subset p hround
        have hs : stochasticRecording (history s.normalize.reference s.normalize.depth) = true := by
          apply s.normalize_ready.resolve_left
          intro ht
          have hz := ReplicaSurvivorEntries.terminal_active_empty s.normalize ht
          have hnonempty := hne.mono hsub
          rw [hz] at hnonempty
          exact Finset.not_nonempty_empty hnonempty
        have hraw := ReplicaSurvivorEntries.raw_count_before_step_le_agents
          reference N w (roundTypes p r) hs hsub
        have hmean : (N + 1 : ℕ) * (((roundTypes p r).card : ℝ) / m) <
            α * (m * q : ℕ) := by
          by_contra hnot
          have h := hgood.full (roundTypes p r) hS (le_of_not_gt hnot)
          exact (not_lt_of_ge hraw) h
        have hprev : s.depth / (m * q) ≤ r :=
          (Nat.div_le_div_right s.le_normalize_depth).trans hround
        rw [rawRoundCount, if_pos hround,
          rawRoundCount_eq_length_of_depth _ r N (Fin.tail w) hprev]
        apply (div_le_div_iff₀ hmR hcard).2
        rw [← mul_div_assoc] at hmean
        exact ((div_lt_iff₀ hmR).1 hmean).le
      · have h := ih (Fin.tail w) hp' hgood.tail
        dsimp only [s] at hround
        simpa only [rawRoundCount, if_neg hround, add_zero] using h

end ProbabilisticSerial.RawPrefixGood
