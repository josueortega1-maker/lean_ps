import LoadBound

/-!
# The deterministic phase recursion

This file formalizes the deterministic part of Proposition 2 in the paper.
It has three layers.

* A block of PS phases cannot consume more than one unit from each good in a
  fixed survivor set.
* If the load event supplies the paper's demand lower bound throughout such a
  block, its contribution to `∫ n / |A(t)| dt` is at most `8 / η`.
* The ceiling recurrence for the active-set sizes implies an exponential
  recurrence after rescaling.  A minimal iterate of the exponential is used as
  a concrete, definitionally finite version of `logStar`.

No probabilistic statement is used below: all results are pathwise facts about
the finite event trace constructed in `PSProcess`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PhaseIntegral

open PSProcess PSProcess.Phase StoppedChoices LoadBound

/-! ## Integrals and consumption on a finite block -/

/-- The event-driven integral restricted to a list of phases. -/
def blockIntegral {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) : ℝ :=
  (phases.map (fun p =>
    p.duration * ((n : ℝ) / (p.active.card : ℝ)))).sum

/-- Total amount consumed from `B` during a list of phases. -/
def blockConsumption {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (phases : List (Phase n profile)) : ℝ :=
  (phases.map (fun p =>
    p.duration * (phaseLoad B p : ℝ))).sum

@[simp] lemma blockIntegral_nil {n : ℕ} {profile : Profile n} :
    blockIntegral ([] : List (Phase n profile)) = 0 := rfl

@[simp] lemma blockIntegral_cons {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (phases : List (Phase n profile)) :
    blockIntegral (p :: phases) =
      p.duration * ((n : ℝ) / (p.active.card : ℝ)) +
        blockIntegral phases := rfl

@[simp] lemma blockConsumption_nil {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) :
    blockConsumption B ([] : List (Phase n profile)) = 0 := rfl

@[simp] lemma blockConsumption_cons {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (p : Phase n profile)
    (phases : List (Phase n profile)) :
    blockConsumption B (p :: phases) =
      p.duration * (phaseLoad B p : ℝ) + blockConsumption B phases := rfl

lemma phase_term_nonneg {n : ℕ} {profile : Profile n}
    (p : Phase n profile) (g : Fin n) :
    0 ≤ p.duration * (p.load g : ℝ) := by
  exact mul_nonneg p.duration_pos.le (Nat.cast_nonneg _)

/-- A nonnegative mapped sum can only decrease when list entries are deleted. -/
lemma sum_map_le_sum_map_of_sublist_of_nonneg {α : Type*}
    {small large : List α} (hsub : small.Sublist large)
    (f : α → ℝ) (hnonneg : ∀ x ∈ large, 0 ≤ f x) :
    (small.map f).sum ≤ (large.map f).sum := by
  induction hsub with
  | slnil => simp
  | @cons l₁ l₂ a hsub ih =>
      have ha : 0 ≤ f a := hnonneg a (by simp)
      have htail : ∀ x ∈ l₂, 0 ≤ f x := by
        intro x hx
        exact hnonneg x (by simp [hx])
      simp only [List.map_cons, List.sum_cons]
      linarith [ih htail]
  | @cons₂ l₁ l₂ a hsub ih =>
      have htail : ∀ x ∈ l₂, 0 ≤ f x := by
        intro x hx
        exact hnonneg x (by simp [hx])
      simpa using add_le_add_left (ih htail) (f a)

lemma const_mul_sum_map {α : Type*} (c : ℝ) (l : List α) (f : α → ℝ) :
    c * (l.map f).sum = (l.map (fun x => c * f x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

/-- Consumption from a set is the sum of the per-good consumptions. -/
lemma blockConsumption_eq_sum_good {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (phases : List (Phase n profile)) :
    blockConsumption B phases =
      ∑ g ∈ B,
        (phases.map (fun p => p.duration * (p.load g : ℝ))).sum := by
  induction phases with
  | nil => simp [blockConsumption]
  | cons p phases ih =>
      rw [blockConsumption_cons, ih]
      simp only [phaseLoad, Nat.cast_sum, Nat.cast_ofNat,
        List.map_cons, List.sum_cons]
      rw [Finset.mul_sum, Finset.sum_add_distrib]

/-- Pathwise supply bound: any sublist of the actual run consumes at most one
unit from each good of `B`.  Contiguity is not needed; `Sublist` is stronger
than the inequality requires. -/
theorem blockConsumption_le_card {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases) :
    blockConsumption B phases ≤ (B.card : ℝ) := by
  rw [blockConsumption_eq_sum_good]
  calc
    (∑ g ∈ B,
        (phases.map (fun p => p.duration * (p.load g : ℝ))).sum)
        ≤ ∑ _g ∈ B, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro g hg
          calc
            (phases.map
                (fun p => p.duration * (p.load g : ℝ))).sum
                ≤ ((run profile).phases.map
                    (fun p => p.duration * (p.load g : ℝ))).sum :=
              sum_map_le_sum_map_of_sublist_of_nonneg hsub _
                (fun p hp => phase_term_nonneg p g)
            _ = 1 := run_consumedByGood profile g
    _ = (B.card : ℝ) := by simp

/-- One survivor block costs at most `8/η` in the eating integral.  This is
the paper's cancellation of the survivor count: demand accumulated by `B` is
bounded above by its remaining supply and below by
`(η/8) |B| n/|A|`. -/
theorem oneBlock_integral_le {n : ℕ} {profile : Profile n}
    {η : ℝ} (hη : 0 < η)
    (B : Finset (Fin n)) (hB : B.Nonempty)
    (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases)
    (hdemand : ∀ p ∈ phases,
      (η / 8) * ((n : ℝ) * (B.card : ℝ) /
        (p.active.card : ℝ)) ≤ (phaseLoad B p : ℝ)) :
    blockIntegral phases ≤ 8 / η := by
  have hBposNat : 0 < B.card := Finset.card_pos.mpr hB
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hBposNat
  have hterm : ∀ p ∈ phases,
      p.duration *
          ((η / 8) * (B.card : ℝ) *
            ((n : ℝ) / (p.active.card : ℝ))) ≤
        p.duration * (phaseLoad B p : ℝ) := by
    intro p hp
    apply mul_le_mul_of_nonneg_left _ p.duration_pos.le
    convert hdemand p hp using 1
    ring
  have hscaled :
      (η / 8) * (B.card : ℝ) * blockIntegral phases ≤
        blockConsumption B phases := by
    unfold blockIntegral blockConsumption
    calc
      (η / 8) * (B.card : ℝ) *
          (phases.map
            (fun p => p.duration * ((n : ℝ) /
              (p.active.card : ℝ)))).sum =
          (phases.map (fun p => p.duration *
            ((η / 8) * (B.card : ℝ) *
              ((n : ℝ) / (p.active.card : ℝ))))).sum := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              const_mul_sum_map ((η / 8) * (B.card : ℝ)) phases
                (fun p => p.duration *
                  ((n : ℝ) / (p.active.card : ℝ)))
      _ ≤ (phases.map
          (fun p => p.duration * (phaseLoad B p : ℝ))).sum := by
            apply List.sum_le_sum
            exact hterm
  have hsupply := blockConsumption_le_card B phases hsub
  have hcoef : 0 < (η / 8) * (B.card : ℝ) := mul_pos (by positivity) hBpos
  apply (le_div_iff₀ hη).mpr
  have hmain :
      (η / 8) * (B.card : ℝ) * blockIntegral phases ≤
        (B.card : ℝ) := hscaled.trans hsupply
  nlinarith

/-! ## The initial and terminal pieces -/

/-- Total time represented by a phase block. -/
def blockDuration {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) : ℝ :=
  (phases.map Phase.duration).sum

lemma blockDuration_nonneg {n : ℕ} {profile : Profile n}
    (phases : List (Phase n profile)) :
    0 ≤ blockDuration phases := by
  unfold blockDuration
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact p.duration_pos.le

lemma blockDuration_le_one {n : ℕ} {profile : Profile n}
    (hn : 0 < n) (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases) :
    blockDuration phases ≤ 1 := by
  unfold blockDuration
  calc
    (phases.map Phase.duration).sum ≤
        ((run profile).phases.map Phase.duration).sum :=
      sum_map_le_sum_map_of_sublist_of_nonneg hsub _
        (fun p hp => p.duration_pos.le)
    _ = 1 := run_totalDuration profile hn

/-- Before the active set first falls below `n/λ₀`, the contribution is at
most `λ₀`, since the whole run lasts one unit of time. -/
theorem initialBlock_integral_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {lambdaZero : ℝ} (hlambdaZero : 0 ≤ lambdaZero)
    (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases)
    (hratio : ∀ p ∈ phases,
      (n : ℝ) / (p.active.card : ℝ) ≤ lambdaZero) :
    blockIntegral phases ≤ lambdaZero := by
  have hterm : ∀ p ∈ phases,
      p.duration * ((n : ℝ) / (p.active.card : ℝ)) ≤
        p.duration * lambdaZero := by
    intro p hp
    exact mul_le_mul_of_nonneg_left (hratio p hp) p.duration_pos.le
  have hsum : blockIntegral phases ≤
      blockDuration phases * lambdaZero := by
    unfold blockIntegral blockDuration
    calc
      (phases.map (fun p =>
          p.duration * ((n : ℝ) / (p.active.card : ℝ)))).sum ≤
          (phases.map (fun p => p.duration * lambdaZero)).sum := by
            apply List.sum_le_sum
            exact hterm
      _ = (phases.map Phase.duration).sum * lambdaZero := by
            exact List.sum_map_mul_right phases Phase.duration lambdaZero
  exact hsum.trans (by
    have htime := blockDuration_le_one hn phases hsub
    nlinarith [blockDuration_nonneg phases])

/-- Once at most two goods remain, a remaining time of at most `2/n` costs
at most two in the eating integral. -/
theorem terminalBlock_integral_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) (phases : List (Phase n profile))
    (_hsmall : ∀ p ∈ phases, p.active.card ≤ 2)
    (htime : blockDuration phases ≤ 2 / (n : ℝ)) :
    blockIntegral phases ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ p ∈ phases,
      p.duration * ((n : ℝ) / (p.active.card : ℝ)) ≤
        p.duration * (n : ℝ) := by
    intro p hp
    have hsNat : 0 < p.active.card := Finset.card_pos.mpr p.active_nonempty
    have hs : (1 : ℝ) ≤ p.active.card := by exact_mod_cast hsNat
    have hratio : (n : ℝ) / (p.active.card : ℝ) ≤ (n : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_left hratio p.duration_pos.le
  have hsum : blockIntegral phases ≤
      blockDuration phases * (n : ℝ) := by
    unfold blockIntegral blockDuration
    calc
      (phases.map (fun p =>
          p.duration * ((n : ℝ) / (p.active.card : ℝ)))).sum ≤
          (phases.map (fun p => p.duration * (n : ℝ))).sum := by
            apply List.sum_le_sum
            exact hterm
      _ = (phases.map Phase.duration).sum * (n : ℝ) := by
            exact List.sum_map_mul_right phases Phase.duration (n : ℝ)
  calc
    blockIntegral phases ≤ blockDuration phases * (n : ℝ) := hsum
    _ ≤ (2 / (n : ℝ)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right htime hnR.le
    _ = 2 := by field_simp

lemma phaseLoad_eq_n_of_active_subset {n : ℕ} {profile : Profile n}
    (B : Finset (Fin n)) (p : Phase n profile)
    (hactive : p.active ⊆ B) :
    phaseLoad B p = n := by
  rw [phaseLoad_eq_card_phaseEaters]
  have heq : phaseEaters B p = Finset.univ := by
    ext i
    simp [phaseEaters, hactive (p.choice_mem_active i)]
  rw [heq]
  simp

/-- The remaining-time estimate is itself a consequence of supply
conservation: if every phase in a sublist eats inside a carrier of size at
most two, those phases can consume at most two units in total. -/
theorem terminalBlock_duration_le {n : ℕ} {profile : Profile n}
    (hn : 0 < n) (B : Finset (Fin n)) (hBcard : B.card ≤ 2)
    (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases)
    (hactive : ∀ p ∈ phases, p.active ⊆ B) :
    blockDuration phases ≤ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcons := blockConsumption_le_card B phases hsub
  have hconsEq : blockConsumption B phases =
      blockDuration phases * (n : ℝ) := by
    unfold blockConsumption blockDuration
    calc
      (phases.map (fun p =>
          p.duration * (phaseLoad B p : ℝ))).sum =
          (phases.map (fun p => p.duration * (n : ℝ))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro p hp
            rw [phaseLoad_eq_n_of_active_subset B p (hactive p hp)]
      _ = (phases.map Phase.duration).sum * (n : ℝ) := by
        exact List.sum_map_mul_right phases Phase.duration (n : ℝ)
  have hBcardR : (B.card : ℝ) ≤ 2 := by exact_mod_cast hBcard
  rw [hconsEq] at hcons
  apply (le_div_iff₀ hnR).2
  exact hcons.trans hBcardR

/-- Concrete terminal estimate using only a two-good carrier and the fact
that the phases form a sublist of the actual run. -/
theorem terminalBlock_integral_le_of_carrier
    {n : ℕ} {profile : Profile n} (hn : 0 < n)
    (B : Finset (Fin n)) (hBcard : B.card ≤ 2)
    (phases : List (Phase n profile))
    (hsub : phases.Sublist (run profile).phases)
    (hactive : ∀ p ∈ phases, p.active ⊆ B) :
    blockIntegral phases ≤ 2 := by
  have hsmall : ∀ p ∈ phases, p.active.card ≤ 2 := by
    intro p hp
    exact (Finset.card_le_card (hactive p hp)).trans hBcard
  apply terminalBlock_integral_le hn phases hsmall
  exact terminalBlock_duration_le hn B hBcard phases hsub hactive

/-! ## The active-size ceiling recurrence -/

/-- The unrounded candidate-set size used in the stopping rule. -/
def candidateBase (n : ℕ) (α lambda : ℝ) : ℝ :=
  (n : ℝ) * Real.exp (-α * lambda)

lemma candidateSize_cast_lt_base_add_one (n : ℕ) (α lambda : ℝ) :
    (candidateSize n α lambda : ℝ) <
      candidateBase n α lambda + 1 := by
  apply Nat.ceil_lt_add_one
  positivity

/-- If the unrounded candidate size is at most one, the next active set has
at most two goods and the phase recursion terminates. -/
theorem nextActive_le_two_of_base_le_one {n next : ℕ} {α lambda : ℝ}
    (hnext : next ≤ 2 * candidateSize n α lambda)
    (hbase : candidateBase n α lambda ≤ 1) :
    next ≤ 2 := by
  have hcand : candidateSize n α lambda ≤ 1 := by
    apply (Nat.ceil_le).2
    simpa [candidateBase] using hbase
  omega

/-- In the nonterminal case the ceiling loses only a factor two. -/
lemma candidateSize_cast_le_two_mul_base {n : ℕ} {α lambda : ℝ}
    (hbase : 1 ≤ candidateBase n α lambda) :
    (candidateSize n α lambda : ℝ) ≤
      2 * candidateBase n α lambda := by
  have hlt := candidateSize_cast_lt_base_add_one n α lambda
  linarith

/-- Writing `λ=n/ℓ`, the active-size recursion
`ℓ' ≤ 2⌈n exp(-αλ)⌉` gives
`λ' ≥ exp(αλ)/4` whenever the unrounded ceiling argument is at least one. -/
theorem nextLambda_ge_exp_div_four {n next : ℕ} {α lambda : ℝ}
    (hn : 0 < n) (hnextPos : 0 < next)
    (hnext : next ≤ 2 * candidateSize n α lambda)
    (hbase : 1 ≤ candidateBase n α lambda) :
    Real.exp (α * lambda) / 4 ≤ (n : ℝ) / (next : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnextRpos : (0 : ℝ) < next := by exact_mod_cast hnextPos
  have hnextR : (next : ℝ) ≤
      2 * (candidateSize n α lambda : ℝ) := by exact_mod_cast hnext
  have hcand := candidateSize_cast_le_two_mul_base hbase
  have hsize : (next : ℝ) ≤
      4 * (n : ℝ) * Real.exp (-α * lambda) := by
    unfold candidateBase at hcand
    nlinarith
  rw [le_div_iff₀ hnextRpos]
  have hmul := mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ Real.exp (α * lambda) / 4 by positivity)
  have hcancel : Real.exp (α * lambda) *
      Real.exp (-α * lambda) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    Real.exp (α * lambda) / 4 * (next : ℝ) ≤
        Real.exp (α * lambda) / 4 *
          (4 * (n : ℝ) * Real.exp (-α * lambda)) := hmul
    _ = (n : ℝ) := by rw [show
        Real.exp (α * lambda) / 4 *
            (4 * (n : ℝ) * Real.exp (-α * lambda)) =
          (n : ℝ) * (Real.exp (α * lambda) *
            Real.exp (-α * lambda)) by ring, hcancel, mul_one]

/-- The paper's absolute choice of `λ₀` turns the preceding recurrence into
`u' ≥ exp u` for `u=αλ/2`. -/
theorem rescaledLambda_next_ge_exp {α lambda lambdaNext : ℝ}
    (hα : 0 < α)
    (hphaseConstant : Real.log (8 / α) ≤ α * lambda / 2)
    (hrecurrence : Real.exp (α * lambda) / 4 ≤ lambdaNext) :
    Real.exp (α * lambda / 2) ≤ α * lambdaNext / 2 := by
  have hratioPos : 0 < 8 / α := div_pos (by norm_num) hα
  have hratio : 8 / α ≤ Real.exp (α * lambda / 2) := by
    calc
      8 / α = Real.exp (Real.log (8 / α)) :=
        (Real.exp_log hratioPos).symm
      _ ≤ Real.exp (α * lambda / 2) :=
        Real.exp_le_exp.mpr hphaseConstant
  have hscaledOne : 1 ≤
      (α / 8) * Real.exp (α * lambda / 2) := by
    have h8 : 8 ≤ α * Real.exp (α * lambda / 2) := by
      have := (div_le_iff₀ hα).mp hratio
      simpa [mul_comm] using this
    calc
      (1 : ℝ) = (1 / 8) * 8 := by norm_num
      _ ≤ (1 / 8) * (α * Real.exp (α * lambda / 2)) :=
        mul_le_mul_of_nonneg_left h8 (by norm_num)
      _ = (α / 8) * Real.exp (α * lambda / 2) := by ring
  have hexpPos := Real.exp_pos (α * lambda / 2)
  have hdouble : Real.exp (α * lambda / 2) ≤
      (α / 8) * Real.exp (α * lambda) := by
    calc
      Real.exp (α * lambda / 2) =
          1 * Real.exp (α * lambda / 2) := by ring
      _ ≤ ((α / 8) * Real.exp (α * lambda / 2)) *
          Real.exp (α * lambda / 2) :=
        mul_le_mul_of_nonneg_right hscaledOne hexpPos.le
      _ = (α / 8) * Real.exp (α * lambda) := by
        rw [mul_assoc]
        rw [← Real.exp_add]
        congr 2
        ring
  have hrecScaled := mul_le_mul_of_nonneg_left hrecurrence
    (show 0 ≤ α / 2 by positivity)
  calc
    Real.exp (α * lambda / 2) ≤
        (α / 8) * Real.exp (α * lambda) := hdouble
    _ = (α / 2) * (Real.exp (α * lambda) / 4) := by ring
    _ ≤ (α / 2) * lambdaNext := hrecScaled
    _ = α * lambdaNext / 2 := by ring

/-- Direct active-cardinality form of the phase recurrence. -/
theorem activeSize_recurrence_gives_exp_scale
    {n active next : ℕ} {α : ℝ}
    (hn : 0 < n) (hnextPos : 0 < next) (hα : 0 < α)
    (hnext : next ≤ 2 * candidateSize n α
      ((n : ℝ) / (active : ℝ)))
    (hbase : 1 ≤ candidateBase n α
      ((n : ℝ) / (active : ℝ)))
    (hphaseConstant : Real.log (8 / α) ≤
      α * ((n : ℝ) / (active : ℝ)) / 2) :
    Real.exp (α * ((n : ℝ) / (active : ℝ)) / 2) ≤
      α * ((n : ℝ) / (next : ℝ)) / 2 := by
  apply rescaledLambda_next_ge_exp hα hphaseConstant
  exact nextLambda_ge_exp_div_four hn hnextPos hnext hbase


/-- Reaching `αλ/2 ≥ log n/2` makes the next candidate base at most one,
so `nextActive_le_two_of_base_le_one` applies. -/
theorem candidateBase_le_one_of_log_threshold {n : ℕ} {α lambda : ℝ}
    (hn : 0 < n)
    (hthreshold : Real.log (n : ℝ) / 2 ≤ α * lambda / 2) :
    candidateBase n α lambda ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (-α * lambda) ≤
      Real.exp (-Real.log (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hlog : Real.exp (Real.log (n : ℝ)) = (n : ℝ) :=
    Real.exp_log hnR
  calc
    candidateBase n α lambda =
        (n : ℝ) * Real.exp (-α * lambda) := rfl
    _ ≤ (n : ℝ) * Real.exp (-Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp hnR.le
    _ = 1 := by
      rw [Real.exp_neg, hlog]
      field_simp

/-! ## A concrete iterated-log counter -/

/-- Iterating `exp` from a fixed starting scale. -/
def iteratedExp (u₀ : ℝ) : ℕ → ℝ
  | 0 => u₀
  | k + 1 => Real.exp (iteratedExp u₀ k)

@[simp] lemma iteratedExp_zero (u₀ : ℝ) : iteratedExp u₀ 0 = u₀ := rfl

@[simp] lemma iteratedExp_succ (u₀ : ℝ) (k : ℕ) :
    iteratedExp u₀ (k + 1) = Real.exp (iteratedExp u₀ k) := rfl

/-- Exponential iteration grows by at least one at every step.  This elementary
bound is enough to prove that the hitting-time definition below is total. -/
lemma add_natCast_le_iteratedExp (u₀ : ℝ) :
    ∀ k : ℕ, u₀ + (k : ℝ) ≤ iteratedExp u₀ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        u₀ + ((k + 1 : ℕ) : ℝ) = (u₀ + (k : ℝ)) + 1 := by
          push_cast
          ring
        _ ≤ iteratedExp u₀ k + 1 := add_le_add_right ih 1
        _ ≤ Real.exp (iteratedExp u₀ k) :=
          Real.add_one_le_exp (iteratedExp u₀ k)
        _ = iteratedExp u₀ (k + 1) := rfl

lemma exists_iteratedExp_ge (u₀ target : ℝ) :
    ∃ k : ℕ, target ≤ iteratedExp u₀ k := by
  obtain ⟨k, hk⟩ := exists_nat_ge (target - u₀)
  refine ⟨k, ?_⟩
  exact (by linarith : target ≤ u₀ + (k : ℝ)).trans
    (add_natCast_le_iteratedExp u₀ k)

/-- The least number of exponential iterations needed to reach `target`.
Equivalently, this is a base-`e`, shifted version of `logStar`; choosing a
different fixed start changes it by only an absolute additive constant. -/
def exponentialHeight (u₀ target : ℝ) : ℕ :=
  Nat.find (exists_iteratedExp_ge u₀ target)

lemma exponentialHeight_spec (u₀ target : ℝ) :
    target ≤ iteratedExp u₀ (exponentialHeight u₀ target) :=
  Nat.find_spec (exists_iteratedExp_ge u₀ target)

/-- Any finite chain satisfying `u_{j+1} ≥ exp(u_j)` and remaining below the
target has length at most `exponentialHeight`. -/
theorem chain_length_le_exponentialHeight
    (u : ℕ → ℝ) (u₀ target : ℝ) (m : ℕ)
    (hstart : u₀ ≤ u 0)
    (hstep : ∀ k, k + 1 < m → Real.exp (u k) ≤ u (k + 1))
    (hbelow : ∀ k, k < m → u k < target) :
    m ≤ exponentialHeight u₀ target := by
  by_contra hnot
  have hheight : exponentialHeight u₀ target < m :=
    Nat.lt_of_not_ge hnot
  have hiter : ∀ k, k ≤ exponentialHeight u₀ target →
      iteratedExp u₀ k ≤ u k := by
    intro k hk
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
        have hkpred : k ≤ exponentialHeight u₀ target :=
          Nat.le_trans (Nat.le_succ k) hk
        have hnextlt : k + 1 < m := lt_of_le_of_lt hk hheight
        calc
          iteratedExp u₀ (k + 1) =
              Real.exp (iteratedExp u₀ k) := rfl
          _ ≤ Real.exp (u k) := Real.exp_le_exp.mpr (ih hkpred)
          _ ≤ u (k + 1) := hstep k hnextlt
  have hreach := exponentialHeight_spec u₀ target
  have hchain := hiter (exponentialHeight u₀ target) le_rfl
  have hstillBelow := hbelow (exponentialHeight u₀ target) hheight
  exact (not_le_of_gt hstillBelow) (hreach.trans hchain)

/-! ## Assembly from certified survivor blocks -/

@[simp] lemma blockIntegral_append {n : ℕ} {profile : Profile n}
    (left right : List (Phase n profile)) :
    blockIntegral (left ++ right) =
      blockIntegral left + blockIntegral right := by
  simp [blockIntegral]

lemma blockIntegral_flatten {n : ℕ} {profile : Profile n}
    (blocks : List (List (Phase n profile))) :
    blockIntegral blocks.flatten =
      (blocks.map blockIntegral).sum := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
      simp [ih]

/-- Data attached to one greedily stopped phase: a survivor set that stays
active through the block and satisfies the load-event demand inequality. -/
structure SurvivorBlock (n : ℕ) (profile : Profile n) (η : ℝ) where
  phases : List (Phase n profile)
  survivor : Finset (Fin n)
  survivor_nonempty : survivor.Nonempty
  phases_sublist : phases.Sublist (run profile).phases
  demand : ∀ p ∈ phases,
    (η / 8) * ((n : ℝ) * (survivor.card : ℝ) /
      (p.active.card : ℝ)) ≤ (phaseLoad survivor p : ℝ)

lemma SurvivorBlock.integral_le {n : ℕ} {profile : Profile n} {η : ℝ}
    (hη : 0 < η) (block : SurvivorBlock n profile η) :
    blockIntegral block.phases ≤ 8 / η :=
  oneBlock_integral_le hη block.survivor block.survivor_nonempty
    block.phases block.phases_sublist block.demand

/-- A certificate exposing exactly the deterministic facts supplied by the
paper's greedy stopping-time construction.  Step 9 constructs this certificate
from the simultaneous load event; the theorem below contains no remaining
analytic or probabilistic gap. -/
structure PhaseCertificate (n : ℕ) (profile : Profile n)
    (η lambdaZero u₀ target : ℝ) where
  initial : List (Phase n profile)
  blocks : List (SurvivorBlock n profile η)
  terminal : List (Phase n profile)
  decomposition : (run profile).phases =
    initial ++ (blocks.map SurvivorBlock.phases).flatten ++ terminal
  initial_sublist : initial.Sublist (run profile).phases
  initial_ratio : ∀ p ∈ initial,
    (n : ℝ) / (p.active.card : ℝ) ≤ lambdaZero
  terminalCarrier : Finset (Fin n)
  terminalCarrier_card : terminalCarrier.card ≤ 2
  terminal_sublist : terminal.Sublist (run profile).phases
  terminal_active : ∀ p ∈ terminal, p.active ⊆ terminalCarrier
  scale : ℕ → ℝ
  scale_start : u₀ ≤ scale 0
  scale_step : ∀ k, k + 1 < blocks.length →
    Real.exp (scale k) ≤ scale (k + 1)
  /-- Every block except possibly the last starts below the terminal scale.
  The last block is the one during which the threshold may be crossed. -/
  scale_below : ∀ k, k + 1 < blocks.length → scale k < target

/-- Fully assembled deterministic phase bound.  The three summands are the
initial interval, the survivor blocks, and the at-most-two-goods tail. -/
theorem eatingIntegral_le_of_phaseCertificate
    {n : ℕ} {profile : Profile n} {η lambdaZero u₀ target : ℝ}
    (hn : 0 < n) (hη : 0 < η) (hlambdaZero : 0 ≤ lambdaZero)
    (cert : PhaseCertificate n profile η lambdaZero u₀ target) :
    eatingIntegral (run profile) ≤
      lambdaZero + (8 / η) *
        ((exponentialHeight u₀ target : ℝ) + 1) + 2 := by
  have hinitial : blockIntegral cert.initial ≤ lambdaZero :=
    initialBlock_integral_le hn hlambdaZero cert.initial
      cert.initial_sublist cert.initial_ratio
  have hterminal : blockIntegral cert.terminal ≤ 2 :=
    terminalBlock_integral_le_of_carrier hn cert.terminalCarrier
      cert.terminalCarrier_card cert.terminal cert.terminal_sublist
      cert.terminal_active
  have hblockEach : ∀ block ∈ cert.blocks,
      blockIntegral block.phases ≤ 8 / η := by
    intro block hblock
    exact block.integral_le hη
  have hblockSum :
      (cert.blocks.map
        (fun block => blockIntegral block.phases)).sum ≤
        (cert.blocks.length : ℝ) * (8 / η) := by
    calc
      (cert.blocks.map
          (fun block => blockIntegral block.phases)).sum ≤
          (cert.blocks.map (fun _ => 8 / η)).sum := by
            apply List.sum_le_sum
            exact hblockEach
      _ = (cert.blocks.length : ℝ) * (8 / η) := by simp
  have hprefixCount : cert.blocks.length - 1 ≤
      exponentialHeight u₀ target := by
    apply chain_length_le_exponentialHeight cert.scale u₀ target
      (cert.blocks.length - 1) cert.scale_start
    · intro k hk
      exact cert.scale_step k (by omega)
    · intro k hk
      exact cert.scale_below k (by omega)
  have hcount : cert.blocks.length ≤
      exponentialHeight u₀ target + 1 := by omega
  have hfactor : 0 ≤ 8 / η := by positivity
  have hblockHeight :
      (cert.blocks.map
        (fun block => blockIntegral block.phases)).sum ≤
        (8 / η) * ((exponentialHeight u₀ target : ℝ) + 1) := by
    have hcountR : (cert.blocks.length : ℝ) ≤
        (exponentialHeight u₀ target : ℝ) + 1 := by
      exact_mod_cast hcount
    calc
      _ ≤ (cert.blocks.length : ℝ) * (8 / η) := hblockSum
      _ ≤ ((exponentialHeight u₀ target : ℝ) + 1) * (8 / η) :=
        mul_le_mul_of_nonneg_right hcountR hfactor
      _ = (8 / η) * ((exponentialHeight u₀ target : ℝ) + 1) := by ring
  have hdecomp : eatingIntegral (run profile) =
      blockIntegral cert.initial +
        (cert.blocks.map
          (fun block => blockIntegral block.phases)).sum +
        blockIntegral cert.terminal := by
    change blockIntegral (run profile).phases = _
    rw [cert.decomposition, blockIntegral_append, blockIntegral_append,
      blockIntegral_flatten]
    simp [Function.comp_def]
  rw [hdecomp]
  linarith

end ProbabilisticSerial.PhaseIntegral
