import ReplicaRawStep
import CouponLowerBound

/-!
# Finite raw-label simulation of the replica choice machine

A state carries a reference profile only as a witness for its nonempty
conditional fiber. Before requesting a new raw label, deterministic copy
queries are skipped. Skipping does not alter the conditional profile law.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawProcess
open ReplicaPS ReplicaChoiceMachine ReplicaRawStep UniformProduct

variable {m q : ℕ} [Nonempty (Fin (m * q))]

lemma fiber_succ_of_nonfresh (reference : ReplicaPS.Profile m q) (depth : ℕ)
    (hs : stochasticRecording (history reference depth) = false) :
    fiber reference (depth + 1) = fiber reference depth := by
  unfold fiber
  rw [pathFiber_eq_compatibleProfiles reference (depth + 1),
    pathFiber_eq_compatibleProfiles reference depth,
    revealHistory_succ, revealStep_eq_none reference depth hs]
  simp

def nextQueryDepth (reference : ReplicaPS.Profile m q) : ℕ → ℕ → ℕ
  | 0, depth => depth
  | fuel + 1, depth =>
      if (m * q) * (m * q) ≤ depth ∨ stochasticRecording (history reference depth) = true then
        depth
      else nextQueryDepth reference fuel (depth + 1)

lemma nextQueryDepth_bounds (reference : ReplicaPS.Profile m q) (fuel depth : ℕ) :
    depth ≤ nextQueryDepth reference fuel depth ∧
      nextQueryDepth reference fuel depth ≤ depth + fuel := by
  induction fuel generalizing depth with
  | zero => simp [nextQueryDepth]
  | succ fuel ih =>
      unfold nextQueryDepth
      split_ifs
      · omega
      · have h := ih (depth + 1)
        omega

theorem nextQueryDepth_ready (reference : ReplicaPS.Profile m q) (fuel depth : ℕ)
    (hf : (m * q) * (m * q) ≤ depth + fuel) :
    (m * q) * (m * q) ≤ nextQueryDepth reference fuel depth ∨
      stochasticRecording (history reference (nextQueryDepth reference fuel depth)) = true := by
  induction fuel generalizing depth with
  | zero => exact Or.inl (by simpa [nextQueryDepth] using hf)
  | succ fuel ih =>
      unfold nextQueryDepth
      split_ifs with h
      · exact h
      · exact ih (depth + 1) (by omega)

theorem nextQueryDepth_fiber (reference : ReplicaPS.Profile m q) (fuel depth : ℕ) :
    fiber reference (nextQueryDepth reference fuel depth) = fiber reference depth := by
  induction fuel generalizing depth with
  | zero => rfl
  | succ fuel ih =>
      unfold nextQueryDepth
      split_ifs with h
      · rfl
      · have hs : stochasticRecording (history reference depth) = false :=
          Bool.eq_false_of_not_eq_true (fun ht => h (Or.inr ht))
        exact (ih (depth + 1)).trans (fiber_succ_of_nonfresh reference depth hs)

structure State (m q : ℕ) where
  reference : ReplicaPS.Profile m q
  depth : ℕ

def State.posterior (s : State m q) (F : ReplicaPS.Profile m q → ℝ) : ℝ :=
  𝔼 profile ∈ fiber s.reference s.depth, F profile

def State.normalize (s : State m q) : State m q :=
  ⟨s.reference, nextQueryDepth s.reference ((m * q) * (m * q)) s.depth⟩

theorem State.normalize_ready (s : State m q) :
    (m * q) * (m * q) ≤ s.normalize.depth ∨
      stochasticRecording (history s.normalize.reference s.normalize.depth) = true :=
  nextQueryDepth_ready s.reference _ s.depth (by omega)

@[simp] theorem State.normalize_fiber (s : State m q) :
    fiber s.normalize.reference s.normalize.depth = fiber s.reference s.depth :=
  nextQueryDepth_fiber _ _ _

@[simp] theorem State.normalize_posterior (s : State m q) (F : ReplicaPS.Profile m q → ℝ) :
    s.normalize.posterior F = s.posterior F := by
  unfold State.posterior
  rw [State.normalize_fiber]

def State.child (s : State m q)
    (hs : stochasticRecording (history s.reference s.depth) = true)
    (g : Fin m) (hg : g ∈ available s.reference s.depth) : State m q :=
  ⟨(acceptedFiber_nonempty s.reference s.depth hs g hg).choose, s.depth + 1⟩

theorem State.child_fiber (s : State m q)
    (hs : stochasticRecording (history s.reference s.depth) = true)
    (g : Fin m) (hg : g ∈ available s.reference s.depth) :
    fiber (s.child hs g hg).reference (s.child hs g hg).depth =
      acceptedFiber s.reference s.depth g := by
  let other := (s.child hs g hg).reference
  have hp : other ∈ acceptedFiber s.reference s.depth g :=
    (acceptedFiber_nonempty s.reference s.depth hs g hg).choose_spec
  rw [acceptedFiber_eq_next_pathFiber s.reference s.depth hs g hg] at hp
  have hh := (Finset.mem_filter.mp hp).2
  change ReplicaChoiceMachine.pathFiber (s.depth + 1)
    (history other (s.depth + 1)) = acceptedFiber s.reference s.depth g
  rw [hh]
  exact (acceptedFiber_eq_next_pathFiber s.reference s.depth hs g hg).symm

def State.step (s : State m q) (g : Fin m) : State m q :=
  let t := s.normalize
  if (m * q) * (m * q) ≤ t.depth then t
  else if hs : stochasticRecording (history t.reference t.depth) = true then
    if hg : g ∈ available t.reference t.depth then (t.child hs g hg).normalize else t
  else t

theorem State.step_ready (s : State m q) (g : Fin m) :
    (m * q) * (m * q) ≤ (s.step g).depth ∨
      stochasticRecording (history (s.step g).reference (s.step g).depth) = true := by
  unfold State.step
  dsimp only
  split_ifs
  all_goals exact State.normalize_ready _

theorem State.fresh_step_posterior (s : State m q)
    (ht : ¬(m * q) * (m * q) ≤ s.normalize.depth)
    (hs : stochasticRecording (history s.normalize.reference s.normalize.depth) = true)
    (g : Fin m) (F : ReplicaPS.Profile m q → ℝ) :
    (𝔼 profile ∈ fiber s.normalize.reference s.normalize.depth,
      rawWeight s.normalize.reference s.normalize.depth profile g * F profile) =
      (1 / (m : ℝ)) * (s.step g).posterior F := by
  by_cases hg : g ∈ available s.normalize.reference s.normalize.depth
  · rw [accepted_weighted_expectation s.normalize.reference s.normalize.depth hs g hg]
    unfold State.step
    simp only [ht, if_false, hs, dif_pos hg, dif_pos, State.normalize_posterior]
    unfold State.posterior
    rw [State.child_fiber]
  · rw [rejected_weighted_expectation s.normalize.reference s.normalize.depth hs g hg]
    unfold State.step
    simp only [ht, if_false, hs, dif_neg hg, dif_pos]
    rfl

/-- One independent uniform raw label preserves the full marginal law of
the original preference profile. This includes any rank or good-event statistic. -/
theorem State.step_posterior_expectation (hm : 0 < m) (s : State m q)
    (F : ReplicaPS.Profile m q → ℝ) :
    (𝔼 g : Fin m, (s.step g).posterior F) = s.posterior F := by
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  by_cases ht : (m * q) * (m * q) ≤ s.normalize.depth
  · simp only [State.step, ht, if_true, State.normalize_posterior]
    exact Finset.expect_const hnonempty _
  · have hs := s.normalize_ready.resolve_left ht
    have h := profile_marginal hm s.normalize.reference s.normalize.depth F
    rw [Finset.expect_sum_comm] at h
    simp_rw [s.fresh_step_posterior ht hs] at h
    rw [← Finset.mul_sum] at h
    change (1 / (m : ℝ)) * (∑ g : Fin m, (s.step g).posterior F) = s.normalize.posterior F at h
    rw [State.normalize_posterior] at h
    rw [Finset.expect_eq_sum_div_card]
    simpa only [Finset.card_univ, Fintype.card_fin, one_div, div_eq_mul_inv,
      mul_comm, mul_one, one_mul] using h

lemma expect_fin_succ {m n : ℕ} (F : (Fin (n + 1) → Fin m) → ℝ) :
    (𝔼 w : Fin (n + 1) → Fin m, F w) =
      𝔼 g : Fin m, 𝔼 w : Fin n → Fin m, F (Fin.cons g w) := by
  calc
    _ = 𝔼 p : Fin m × (Fin n → Fin m), F (Fin.cons p.1 p.2) :=
      Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin m)).symm
        F (fun p => F (Fin.cons p.1 p.2)) (by intro w; simp)
    _ = _ := by
      simpa using Finset.expect_product (Finset.univ : Finset (Fin m))
        (Finset.univ : Finset (Fin n → Fin m)) (fun p => F (Fin.cons p.1 p.2))

/-- Tuples are newest first, consistently with the copy-history convention. -/
def State.evolve (s : State m q) : (n : ℕ) → (Fin n → Fin m) → State m q
  | 0, _ => s
  | n + 1, w => (s.evolve n (Fin.tail w)).step (w 0)

theorem State.evolve_posterior_expectation (hm : 0 < m) (s : State m q)
    (F : ReplicaPS.Profile m q → ℝ) (n : ℕ) :
    (𝔼 w : Fin n → Fin m, (s.evolve n w).posterior F) = s.posterior F := by
  induction n with
  | zero =>
      simp only [State.evolve]
      exact Finset.expect_const (by simp) _
  | succ n ih =>
      rw [expect_fin_succ]
      simp only [State.evolve, Fin.tail_cons, Fin.cons_zero]
      rw [Finset.expect_comm]
      simp_rw [State.step_posterior_expectation hm]
      exact ih

def initialState (reference : ReplicaPS.Profile m q) : State m q := ⟨reference, 0⟩

lemma initialState_fiber (reference : ReplicaPS.Profile m q) :
    fiber (initialState reference).reference (initialState reference).depth =
      ReplicaPS.profileSample m q := by
  ext profile
  simp [initialState, fiber, ReplicaChoiceMachine.pathFiber,
    history, PSChoiceMachine.profileHistory_zero]

/-- Exact profile-law preservation for every finite iid raw-label prefix.
No claim about independent accepted choices is needed or made. -/
theorem raw_prefix_profile_marginal (hm : 0 < m) (reference : ReplicaPS.Profile m q)
    (F : ReplicaPS.Profile m q → ℝ) (n : ℕ) :
    (𝔼 w ∈ CouponLowerBound.labelSample m n, ((initialState reference).evolve n w).posterior F) =
      𝔼 profile ∈ ReplicaPS.profileSample m q, F profile := by
  have hsample : CouponLowerBound.labelSample m n = Finset.univ := by
    simp [CouponLowerBound.labelSample, UniformProduct.productSample]
  rw [hsample, State.evolve_posterior_expectation hm]
  unfold State.posterior
  rw [initialState_fiber]

end ProbabilisticSerial.ReplicaRawProcess
