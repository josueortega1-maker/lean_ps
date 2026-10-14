import ReplicaRawProcess
import ReplicaCapacity

/-! The raw simulation has the clock and nested active sets of the actual PS run. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawProcess
open ReplicaPS ReplicaChoiceMachine ReplicaRawStep

variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma queryTime_at_depth (profile : ReplicaPS.Profile m q) (depth : ℕ) :
    PSChoiceMachine.queryTime (history profile depth) = roundTime profile (depth / (m * q)) := by
  unfold PSChoiceMachine.queryTime
  rw [(PSChoiceMachine.profile_machine_correspondence (liftedProfile profile) depth).1]
  rfl

def State.clock (s : State m q) : ℝ := PSChoiceMachine.queryTime (history s.reference s.depth)

def State.active (s : State m q) : Finset (Fin m) := available s.reference s.depth

lemma State.clock_eq_roundTime (s : State m q) :
    s.clock = roundTime s.reference (s.depth / (m * q)) := queryTime_at_depth _ _

lemma State.clock_nonneg (s : State m q) : 0 ≤ s.clock := by
  rw [s.clock_eq_roundTime]
  exact roundTime_nonneg _ _

lemma State.clock_le_one (s : State m q) : s.clock ≤ 1 := by
  rw [s.clock_eq_roundTime]
  exact roundTime_le_one _ _

lemma State.clock_on_fiber (s : State m q) (profile : ReplicaPS.Profile m q)
    (hp : profile ∈ fiber s.reference s.depth) :
    s.clock = roundTime profile (s.depth / (m * q)) := by
  have hh : history profile s.depth = history s.reference s.depth := (Finset.mem_filter.mp hp).2
  unfold State.clock
  rw [← hh, queryTime_at_depth]

lemma State.active_on_fiber (s : State m q) (profile : ReplicaPS.Profile m q)
    (hp : profile ∈ fiber s.reference s.depth) :
    s.active = roundTypes profile (s.depth / (m * q)) := by
  have hh : history profile s.depth = history s.reference s.depth := (Finset.mem_filter.mp hp).2
  unfold State.active available
  rw [← hh, queryTypes_at_depth]

lemma State.reference_mem_fiber (s : State m q) : s.reference ∈ fiber s.reference s.depth := by
  simp [fiber, ReplicaChoiceMachine.pathFiber, ReplicaRevelation.profileSample_eq_univ]

lemma State.le_normalize_depth (s : State m q) : s.depth ≤ s.normalize.depth :=
  (nextQueryDepth_bounds s.reference _ s.depth).1

lemma State.step_depth_mono (s : State m q) (g : Fin m) : s.depth ≤ (s.step g).depth := by
  unfold State.step
  dsimp only
  split_ifs with ht hs hg
  · exact s.le_normalize_depth
  · exact s.le_normalize_depth.trans
      ((Nat.le_succ _).trans (s.normalize.child hs g hg).le_normalize_depth)
  · exact s.le_normalize_depth
  · exact s.le_normalize_depth

theorem State.step_fiber_subset (s : State m q) (g : Fin m) :
    fiber (s.step g).reference (s.step g).depth ⊆ fiber s.reference s.depth := by
  unfold State.step
  dsimp only
  split_ifs with ht hs hg
  · rw [State.normalize_fiber]
  · rw [State.normalize_fiber, State.child_fiber]
    apply (Finset.filter_subset _ _).trans
    rw [State.normalize_fiber]
  · rw [State.normalize_fiber]
  · rw [State.normalize_fiber]

theorem State.step_clock_mono (s : State m q) (g : Fin m) : s.clock ≤ (s.step g).clock := by
  have hp := s.step_fiber_subset g (s.step g).reference_mem_fiber
  rw [s.clock_on_fiber (s.step g).reference hp, (s.step g).clock_eq_roundTime]
  exact roundTime_mono _ (Nat.div_le_div_right (s.step_depth_mono g))

theorem State.step_active_subset (s : State m q) (g : Fin m) : (s.step g).active ⊆ s.active := by
  have hp := s.step_fiber_subset g (s.step g).reference_mem_fiber
  rw [s.active_on_fiber (s.step g).reference hp,
    (s.step g).active_on_fiber (s.step g).reference (s.step g).reference_mem_fiber]
  exact roundTypes_subset _ (Nat.div_le_div_right (s.step_depth_mono g))

theorem State.normalize_clock_mono (s : State m q) : s.clock ≤ s.normalize.clock := by
  rw [s.clock_eq_roundTime, s.normalize.clock_eq_roundTime]
  exact roundTime_mono _ (Nat.div_le_div_right s.le_normalize_depth)

theorem State.normalize_active_subset (s : State m q) : s.normalize.active ⊆ s.active := by
  change queryTypes (history s.reference s.normalize.depth) ⊆ queryTypes (history s.reference s.depth)
  rw [queryTypes_at_depth, queryTypes_at_depth]
  exact roundTypes_subset _ (Nat.div_le_div_right s.le_normalize_depth)

theorem State.terminal_clock (s : State m q) (ht : (m * q) * (m * q) ≤ s.depth) : s.clock = 1 := by
  have hn : 0 < m * q := PSChoiceMachine.market_pos
  have hdiv : m * q ≤ s.depth / (m * q) := by
    have h := (Nat.div_le_div_right ht : (m * q) * (m * q) / (m * q) ≤ s.depth / (m * q))
    simpa [Nat.ne_of_gt hn] using h
  have hmono := roundTime_mono s.reference hdiv
  rw [roundTime_terminal, ← s.clock_eq_roundTime] at hmono
  exact le_antisymm s.clock_le_one hmono

end ProbabilisticSerial.ReplicaRawProcess
