import UniformRawPrefixes
import ReplicaRawClock
import RawSubsetCounts

/-! Prefix consistency and predictable weighted raw-label counts. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRawProcess
open ReplicaPS ReplicaRawStep UniformRawPrefixes

variable {m q : ℕ} [Nonempty (Fin (m * q))]

theorem State.evolve_depth_mono (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    s.depth ≤ (s.evolve n w).depth := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (ih (Fin.tail w)).trans ((s.evolve n (Fin.tail w)).step_depth_mono (w 0))

theorem State.evolve_fiber_subset (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    fiber (s.evolve n w).reference (s.evolve n w).depth ⊆ fiber s.reference s.depth := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ((s.evolve n (Fin.tail w)).step_fiber_subset (w 0)).trans (ih (Fin.tail w))

theorem State.evolve_clock_mono (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    s.clock ≤ (s.evolve n w).clock := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (ih (Fin.tail w)).trans ((s.evolve n (Fin.tail w)).step_clock_mono (w 0))

theorem State.evolve_active_subset (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    (s.evolve n w).active ⊆ s.active := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ((s.evolve n (Fin.tail w)).step_active_subset (w 0)).trans (ih (Fin.tail w))

theorem State.prefix_fiber_subset (s : State m q) (k r : ℕ)
    (w : Fin (k + r) → Fin m) :
    fiber (s.evolve (k + r) w).reference (s.evolve (k + r) w).depth ⊆
      fiber (s.evolve k (dropNewest k r w)).reference
        (s.evolve k (dropNewest k r w)).depth := by
  induction r with
  | zero => rfl
  | succ r ih =>
      exact ((s.evolve (k + r) (Fin.tail w)).step_fiber_subset (w 0)).trans
        (ih (Fin.tail w))

theorem State.prefix_clock_mono (s : State m q) (k r : ℕ)
    (w : Fin (k + r) → Fin m) :
    (s.evolve k (dropNewest k r w)).clock ≤ (s.evolve (k + r) w).clock := by
  induction r with
  | zero => rfl
  | succ r ih =>
      exact (ih (Fin.tail w)).trans
        ((s.evolve (k + r) (Fin.tail w)).step_clock_mono (w 0))

theorem State.prefix_active_subset (s : State m q) (k r : ℕ)
    (w : Fin (k + r) → Fin m) :
    (s.evolve (k + r) w).active ⊆ (s.evolve k (dropNewest k r w)).active := by
  induction r with
  | zero => rfl
  | succ r ih =>
      exact ((s.evolve (k + r) (Fin.tail w)).step_active_subset (w 0)).trans
        (ih (Fin.tail w))

def weightedRawSum (s : State m q) (W : State m q → ℝ) :
    (n : ℕ) → (Fin n → Fin m) → ℝ
  | 0, _ => 0
  | n + 1, w => weightedRawSum s W n (Fin.tail w) + W (s.evolve n (Fin.tail w))

def weightedRawHits (s : State m q) (W : State m q → ℝ) (S : Finset (Fin m)) :
    (n : ℕ) → (Fin n → Fin m) → ℝ
  | 0, _ => 0
  | n + 1, w => weightedRawHits s W S n (Fin.tail w) +
      W (s.evolve n (Fin.tail w)) * RawSubsetCounts.hit S (w 0)

/-- Weights may depend on the whole past PS history, but are evaluated before
the next independent raw label. -/
theorem expected_weightedRawHits (hm : 0 < m) (s : State m q)
    (W : State m q → ℝ) (S : Finset (Fin m)) (n : ℕ) :
    (𝔼 w : Fin n → Fin m, weightedRawHits s W S n w) =
      (S.card / (m : ℝ)) * (𝔼 w : Fin n → Fin m, weightedRawSum s W n w) := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  induction n with
  | zero => simp [weightedRawHits, weightedRawSum]
  | succ n ih =>
      rw [expect_fin_succ, expect_fin_succ]
      simp only [weightedRawHits, weightedRawSum, Fin.tail_cons, Fin.cons_zero]
      simp_rw [Finset.expect_comm (Finset.univ : Finset (Fin m))
        (Finset.univ : Finset (Fin n → Fin m))]
      simp_rw [Finset.expect_add_distrib, Finset.expect_const hne,
        ← Finset.mul_expect, RawSubsetCounts.expect_hit]
      rw [ih]
      simp_rw [← Finset.expect_mul]
      ring

lemma weightedRawSum_nonneg (s : State m q) (W : State m q → ℝ)
    (hW : ∀ t, 0 ≤ W t) (n : ℕ) (w : Fin n → Fin m) :
    0 ≤ weightedRawSum s W n w := by
  induction n with
  | zero => rfl
  | succ n ih => exact add_nonneg (ih (Fin.tail w)) (hW _)

def remainingWeight (s : State m q) : ℝ := 1 - s.normalize.clock

lemma remainingWeight_bounds (s : State m q) :
    0 ≤ remainingWeight s ∧ remainingWeight s ≤ 1 :=
  ⟨sub_nonneg.mpr s.normalize.clock_le_one, by
    unfold remainingWeight
    linarith [s.normalize.clock_nonneg]⟩

def rawBandCost (s : State m q) (n : ℕ) (w : Fin n → Fin m) : ℝ :=
  weightedRawSum s remainingWeight n w / m

theorem rawBandCost_nonneg (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    0 ≤ rawBandCost s n w :=
  div_nonneg (weightedRawSum_nonneg s remainingWeight
    (fun t => (remainingWeight_bounds t).1) n w) (Nat.cast_nonneg _)

theorem rawBandCost_le_length (s : State m q) (n : ℕ) (w : Fin n → Fin m) :
    rawBandCost s n w ≤ n / (m : ℝ) := by
  have hsum : weightedRawSum s remainingWeight n w ≤ n := by
    induction n with
    | zero => simp [weightedRawSum]
    | succ n ih =>
        have h := (remainingWeight_bounds (s.evolve n (Fin.tail w))).2
        simp only [weightedRawSum, Nat.cast_add, Nat.cast_one]
        linarith [ih (Fin.tail w)]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem expected_hits_per_type (hm : 0 < m) (s : State m q)
    (S : Finset (Fin m)) (hS : S.Nonempty) (n : ℕ) :
    (𝔼 w : Fin n → Fin m, weightedRawHits s remainingWeight S n w / S.card) =
      𝔼 w : Fin n → Fin m, rawBandCost s n w := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  simp only [rawBandCost, ← Finset.expect_div]
  rw [expected_weightedRawHits hm]
  field_simp
  <;> ring

theorem State.evolve_appendNew (s : State m q) (k r : ℕ)
    (old : Fin k → Fin m) (new : Fin r → Fin m) :
    s.evolve (k + r) (appendNew old r new) = (s.evolve k old).evolve r new := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [appendNew, State.evolve, Fin.tail_cons, Fin.cons_zero]
      exact congrArg (fun t : State m q => t.step (new 0)) (ih (Fin.tail new))

theorem weightedRawSum_appendNew (s : State m q) (W : State m q → ℝ)
    (k r : ℕ) (old : Fin k → Fin m) (new : Fin r → Fin m) :
    weightedRawSum s W (k + r) (appendNew old r new) =
      weightedRawSum s W k old + weightedRawSum (s.evolve k old) W r new := by
  induction r with
  | zero => simp [appendNew, weightedRawSum]
  | succ r ih =>
      simp only [appendNew, weightedRawSum, Fin.tail_cons, Fin.cons_zero]
      exact (congrArg₂ (fun a b : ℝ => a + b) (ih (Fin.tail new))
        (congrArg W (State.evolve_appendNew s k r old (Fin.tail new)))).trans (add_assoc _ _ _)

theorem expected_restart (hm : 0 < m) (s : State m q) (k r : ℕ)
    (F : State m q → ℝ) :
    (𝔼 old : Fin k → Fin m, 𝔼 new : Fin r → Fin m, F ((s.evolve k old).evolve r new)) =
      𝔼 w : Fin (k + r) → Fin m, F (s.evolve (k + r) w) := by
  rw [expect_appendNew hm k r]
  simp_rw [State.evolve_appendNew]

theorem expected_bandCost_add (hm : 0 < m) (s : State m q) (k r : ℕ) :
    (𝔼 w : Fin (k + r) → Fin m, rawBandCost s (k + r) w) =
      (𝔼 old : Fin k → Fin m, rawBandCost s k old) +
        𝔼 old : Fin k → Fin m, 𝔼 new : Fin r → Fin m,
          rawBandCost (s.evolve k old) r new := by
  have hnew : (Finset.univ : Finset (Fin r → Fin m)).Nonempty :=
    ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
  rw [expect_appendNew hm k r]
  simp only [rawBandCost, weightedRawSum_appendNew, add_div,
    Finset.expect_add_distrib, Finset.expect_const hnew]

theorem expected_rawCost_mono (hm : 0 < m) (s : State m q) {a b : ℕ} (hab : a ≤ b) :
    (𝔼 w : Fin a → Fin m, rawBandCost s a w) ≤ 𝔼 w : Fin b → Fin m, rawBandCost s b w := by
  have h := expected_bandCost_add hm s a (b - a)
  rw [Nat.add_sub_of_le hab] at h
  have hband : 0 ≤ 𝔼 old : Fin a → Fin m, 𝔼 new : Fin (b - a) → Fin m,
      rawBandCost (s.evolve a old) (b - a) new :=
    Finset.expect_nonneg (fun old _ => Finset.expect_nonneg (fun new _ => rawBandCost_nonneg _ _ _))
  linarith

end ProbabilisticSerial.ReplicaRawProcess
