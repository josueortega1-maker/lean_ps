import PhaseIntegral

/-!
# From the load event to the concrete phase certificate

This file constructs the adapter promised after Step 8.  It defines the
simultaneous load-good event on the actual event-driven PS trace, cuts off the
bounded initial segment, greedily groups the remaining phases at the paper's
threshold `2⌈n exp (-αλ)⌉`, and turns every group into a `SurvivorBlock`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.PhaseAdapter

open PSProcess PSProcess.Phase SequentialRevelation
open StoppedChoices LoadBound PhaseIntegral

/-! ## One absolute threshold satisfying both Steps 7 and 8 -/

/-- All large-`λ` inequalities used by the load union bound and the phase
recursion, collected in one predicate. -/
def PhaseLambdaConditions (lambdaZero : ℝ) : Prop :=
  0 < lambdaZero ∧
    ∀ lambda : ℝ, lambdaZero ≤ lambda →
      1 / alphaZero ≤ lambda ∧
      1 + alphaZero * lambda ≤ (betaZero / 2) * lambda ∧
      2 * lambda * Real.exp (-alphaZero * lambda) ≤ 1 / 4 ∧
      Real.log (8 / alphaZero) ≤ alphaZero * lambda / 2

theorem exists_phaseLambdaZero :
    ∃ lambdaZero : ℝ, PhaseLambdaConditions lambdaZero := by
  obtain ⟨base, hbasePos, hbase⟩ := exists_absolute_lambdaZero
  let lambdaZero := max base
    (2 * Real.log (8 / alphaZero) / alphaZero)
  have hlambdaPos : 0 < lambdaZero :=
    hbasePos.trans_le (le_max_left _ _)
  refine ⟨lambdaZero, hlambdaPos, ?_⟩
  intro lambda hlambda
  have hbaseLe : base ≤ lambda :=
    (le_max_left _ _).trans hlambda
  obtain ⟨hinv, hlinear, hdecay⟩ := hbase lambda hbaseLe
  have hlogLe : 2 * Real.log (8 / alphaZero) / alphaZero ≤ lambda :=
    (le_max_right _ _).trans hlambda
  have hscaled : 2 * Real.log (8 / alphaZero) ≤
      lambda * alphaZero := by
    exact (div_le_iff₀ alphaZero_pos).mp hlogLe
  refine ⟨hinv, hlinear, hdecay, ?_⟩
  nlinarith

/-- A fixed concrete absolute threshold. -/
def phaseLambdaZero : ℝ := Classical.choose exists_phaseLambdaZero

theorem phaseLambdaZero_spec : PhaseLambdaConditions phaseLambdaZero :=
  Classical.choose_spec exists_phaseLambdaZero

lemma phaseLambdaZero_pos : 0 < phaseLambdaZero :=
  phaseLambdaZero_spec.1

/-! ## The concrete simultaneous load event -/

/-- The Step 7 underload conclusion, stated simultaneously for every phase of
the actual PS run whose inverse active fraction exceeds `lambdaZero`. -/
def ConcretePhaseLoadGood {n : ℕ} (profile : Profile n)
    (lambdaZero : ℝ) : Prop :=
  ∀ p ∈ (run profile).phases,
    lambdaZero ≤ (n : ℝ) / (p.active.card : ℝ) →
      (underloadedGoods p.active p.load
        ((etaZero / 4) *
          ((n : ℝ) / (p.active.card : ℝ)))).card <
        candidateSize n alphaZero
          ((n : ℝ) / (p.active.card : ℝ))

noncomputable instance concretePhaseLoadGoodDecidable {n : ℕ}
    (profile : Profile n) (lambdaZero : ℝ) :
    Decidable (ConcretePhaseLoadGood profile lambdaZero) :=
  Classical.propDecidable _

/-- On the concrete good event, every sufficiently large survivor set has the
paper's demand lower bound in every eligible phase. -/
theorem concretePhaseLoadGood_demand {n : ℕ} {profile : Profile n}
    {lambdaZero : ℝ} (hgood : ConcretePhaseLoadGood profile lambdaZero)
    (p : Phase n profile) (hp : p ∈ (run profile).phases)
    (hlambda : lambdaZero ≤
      (n : ℝ) / (p.active.card : ℝ))
    (T : Finset (Fin n)) (hTactive : T ⊆ p.active)
    (hTlarge : 2 * candidateSize n alphaZero
      ((n : ℝ) / (p.active.card : ℝ)) ≤ T.card) :
    (etaZero / 8) *
        ((n : ℝ) * (T.card : ℝ) / (p.active.card : ℝ)) ≤
      (phaseLoad T p : ℝ) := by
  have hs : (0 : ℝ) < p.active.card := by
    exact_mod_cast Finset.card_pos.mpr p.active_nonempty
  have hpaper := paper_demand_bound p.active p.load etaZero_pos.le
    (Nat.cast_nonneg n) hs (hgood p hp hlambda) T hTactive hTlarge
  simpa [setLoad, phaseLoad, Nat.cast_sum] using hpaper

/-! ## Elementary active-cardinality facts -/

/-- The inverse active fraction increases when the active set shrinks. -/
lemma inverseCard_mono {n : ℕ} {profile : Profile n}
    {earlier later : Phase n profile}
    (hsubset : later.active ⊆ earlier.active) :
    (n : ℝ) / (earlier.active.card : ℝ) ≤
      (n : ℝ) / (later.active.card : ℝ) := by
  have hlater : (0 : ℝ) < later.active.card := by
    exact_mod_cast Finset.card_pos.mpr later.active_nonempty
  have hcard : later.active.card ≤ earlier.active.card :=
    Finset.card_le_card hsubset
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hlater
    (by exact_mod_cast hcard)

/-- The decay condition chosen in Step 7 guarantees that the greedy threshold
is strictly below every eligible active cardinality larger than two. -/
theorem twice_candidateSize_lt_activeCard {n active : ℕ}
    (hactive : 2 < active)
    {lambdaZero : ℝ} (hconditions : PhaseLambdaConditions lambdaZero)
    (hlambda : lambdaZero ≤ (n : ℝ) / (active : ℝ)) :
    2 * candidateSize n alphaZero ((n : ℝ) / (active : ℝ)) < active := by
  let lambda : ℝ := (n : ℝ) / (active : ℝ)
  have hactiveR : (0 : ℝ) < active := by positivity
  have hdecay := (hconditions.2 lambda (by simpa [lambda] using hlambda)).2.2.1
  have hceil := candidateSize_cast_lt_base_add_one n alphaZero lambda
  have hbaseEq : candidateBase n alphaZero lambda =
      (active : ℝ) * lambda * Real.exp (-alphaZero * lambda) := by
    unfold candidateBase lambda
    field_simp
  rw [hbaseEq] at hceil
  have htwiceBase :
      2 * ((active : ℝ) * lambda *
        Real.exp (-alphaZero * lambda)) ≤ (active : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_left hdecay
      (show (0 : ℝ) ≤ active by positivity)
    nlinarith
  have hactiveThree : (3 : ℝ) ≤ active := by exact_mod_cast hactive
  have hcast :
      (2 * candidateSize n alphaZero lambda : ℕ) < active := by
    exact_mod_cast (show
      (2 * candidateSize n alphaZero lambda : ℝ) < (active : ℝ) by
        nlinarith)
  simpa [lambda] using hcast

/-! ## Cutting the finite phase list -/

lemma mem_takeWhile_true {γ : Type*} (pred : γ → Bool)
    (xs : List γ) {x : γ} (hx : x ∈ xs.takeWhile pred) :
    pred x = true := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      by_cases hy : pred y = true
      · rw [List.takeWhile_cons_of_pos hy] at hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hy
        · exact ih hx
      · rw [List.takeWhile_cons_of_neg hy] at hx
        simp at hx

/-- If a predicate propagates backwards along a pairwise ordered list, every
entry remaining after `dropWhile pred` fails the predicate. -/
lemma mem_dropWhile_false_of_pairwise {γ : Type*}
    (R : γ → γ → Prop) (P : γ → Prop) [DecidablePred P]
    (xs : List γ) (hpair : xs.Pairwise R)
    (hback : ∀ {earlier later}, R earlier later → P later → P earlier)
    {x : γ} (hx : x ∈ xs.dropWhile (fun y => decide (P y))) :
    ¬ P x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.pairwise_cons] at hpair
      by_cases hy : P y
      · rw [List.dropWhile_cons_of_pos (by simp [hy])] at hx
        exact ih hpair.2 hx
      · rw [List.dropWhile_cons_of_neg (by simp [hy])] at hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hy
        · intro hPx
          exact hy (hback (hpair.1 x hx) hPx)

def phaseRatio {n : ℕ} {profile : Profile n}
    (p : Phase n profile) : ℝ :=
  (n : ℝ) / (p.active.card : ℝ)

def initialPhases {n : ℕ} {profile : Profile n}
    (lambdaZero : ℝ) (phases : List (Phase n profile)) :
    List (Phase n profile) :=
  phases.takeWhile (fun p => decide (phaseRatio p ≤ lambdaZero))

def postInitialPhases {n : ℕ} {profile : Profile n}
    (lambdaZero : ℝ) (phases : List (Phase n profile)) :
    List (Phase n profile) :=
  phases.dropWhile (fun p => decide (phaseRatio p ≤ lambdaZero))

lemma initial_append_postInitial {n : ℕ} {profile : Profile n}
    (lambdaZero : ℝ) (phases : List (Phase n profile)) :
    initialPhases lambdaZero phases ++
      postInitialPhases lambdaZero phases = phases := by
  exact List.takeWhile_append_dropWhile

lemma initialPhases_ratio_le {n : ℕ} {profile : Profile n}
    (lambdaZero : ℝ) (phases : List (Phase n profile))
    {p : Phase n profile} (hp : p ∈ initialPhases lambdaZero phases) :
    phaseRatio p ≤ lambdaZero := by
  apply of_decide_eq_true
  exact mem_takeWhile_true
    (fun q : Phase n profile => decide (phaseRatio q ≤ lambdaZero))
    phases (by simpa [initialPhases] using hp)

lemma postInitialPhases_ratio_gt {n : ℕ} {profile : Profile n}
    (lambdaZero : ℝ) (phases : List (Phase n profile))
    (hpair : phases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active))
    {p : Phase n profile} (hp : p ∈ postInitialPhases lambdaZero phases) :
    lambdaZero < phaseRatio p := by
  have hnot := mem_dropWhile_false_of_pairwise
    (fun earlier later : Phase n profile => later.active ⊂ earlier.active)
    (fun q => phaseRatio q ≤ lambdaZero) phases hpair
    (fun hsub hle => (inverseCard_mono hsub.subset).trans hle) hp
  exact lt_of_not_ge hnot

/-- The cardinality at which the phase beginning at `p` stops. -/
def phaseThreshold {n : ℕ} {profile : Profile n}
    (α : ℝ) (p : Phase n profile) : ℕ :=
  2 * candidateSize n α (phaseRatio p)

/-- Raw greedy grouping.  A block beginning at `p` contains `p` and every
following phase whose active cardinality is still above `phaseThreshold p`.
Recursion continues with the first phase at or below that threshold; once the
head has at most two active goods, the entire suffix is terminal. -/
def greedyRawBlocks {n : ℕ} {profile : Profile n} (α : ℝ) :
    List (Phase n profile) →
      List (List (Phase n profile)) × List (Phase n profile)
  | [] => ([], [])
  | p :: ps =>
      if p.active.card ≤ 2 then
        ([], p :: ps)
      else
        let pred := fun q : Phase n profile =>
          decide (phaseThreshold α p < q.active.card)
        let pre := ps.takeWhile pred
        let remaining := ps.dropWhile pred
        let tail := greedyRawBlocks α remaining
        ((p :: pre) :: tail.1, tail.2)
termination_by phases => phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := ps)
    (fun q : Phase n profile =>
      decide (phaseThreshold α p < q.active.card))).length_le
  simp only [List.length_cons]
  omega

theorem greedyRawBlocks_decomposition {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile)) :
    (greedyRawBlocks α phases).1.flatten ++
      (greedyRawBlocks α phases).2 = phases := by
  cases phases with
  | nil => simp [greedyRawBlocks]
  | cons p ps =>
    rw [greedyRawBlocks]
    split
    next hsmall => rfl
    next hlarge =>
      dsimp only
      let pred := fun q : Phase n profile =>
        decide (phaseThreshold α p < q.active.card)
      let pre := ps.takeWhile pred
      let remaining := ps.dropWhile pred
      have ih := greedyRawBlocks_decomposition α remaining
      change (p :: pre) ++
          (greedyRawBlocks α remaining).1.flatten ++
          (greedyRawBlocks α remaining).2 = p :: ps
      simp only [List.cons_append, List.cons.injEq, true_and]
      calc
        pre ++ (greedyRawBlocks α remaining).1.flatten ++
            (greedyRawBlocks α remaining).2 =
            pre ++ ((greedyRawBlocks α remaining).1.flatten ++
              (greedyRawBlocks α remaining).2) := by
                simp [List.append_assoc]
        _ = pre ++ remaining := by rw [ih]
        _ = ps := by
          exact List.takeWhile_append_dropWhile
termination_by phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := tail)
    (fun q : Phase n profile =>
      decide (phaseThreshold α head < q.active.card))).length_le
  simp only [List.length_cons]
  omega

lemma sublist_flatten_of_mem {γ : Type*} {block : List γ}
    {blocks : List (List γ)} (hblock : block ∈ blocks) :
    block.Sublist blocks.flatten := by
  induction blocks with
  | nil => simp at hblock
  | cons first rest ih =>
      simp only [List.mem_cons] at hblock
      rcases hblock with rfl | hblock
      · exact List.sublist_append_left _ _
      · exact (ih hblock).trans (List.sublist_append_right _ _)

lemma greedyRawBlock_sublist {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases block : List (Phase n profile))
    (hblock : block ∈ (greedyRawBlocks α phases).1) :
    block.Sublist phases := by
  have hflat := sublist_flatten_of_mem hblock
  have hdecomp := greedyRawBlocks_decomposition α phases
  rw [← hdecomp]
  exact hflat.trans (List.sublist_append_left _ _)

lemma greedyRawTerminal_sublist {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile)) :
    (greedyRawBlocks α phases).2.Sublist phases := by
  have hdecomp := greedyRawBlocks_decomposition α phases
  have hwhole :
      ((greedyRawBlocks α phases).1.flatten ++
        (greedyRawBlocks α phases).2).Sublist phases := by
    rw [hdecomp]
  exact (List.sublist_append_right _ _).trans hwhole

lemma head_dropWhile_false {γ : Type*} (pred : γ → Bool)
    (xs : List γ) {y : γ} {ys : List γ}
    (heq : xs.dropWhile pred = y :: ys) :
    ¬ pred y = true := by
  induction xs with
  | nil => simp at heq
  | cons x xs ih =>
      by_cases hx : pred x = true
      · rw [List.dropWhile_cons_of_pos hx] at heq
        exact ih heq
      · rw [List.dropWhile_cons_of_neg hx] at heq
        injection heq with hxy hrest
        simpa [hxy] using hx

/-- Every raw block begins above two and is nonempty. -/
theorem greedyRawBlocks_shape {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases block : List (Phase n profile))
    (hblock : block ∈ (greedyRawBlocks α phases).1) :
    ∃ first rest, block = first :: rest ∧ 2 < first.active.card := by
  cases phases with
  | nil => simp [greedyRawBlocks] at hblock
  | cons p ps =>
    rw [greedyRawBlocks] at hblock
    split at hblock
    next hsmall => simp at hblock
    next hlarge =>
      simp only [List.mem_cons] at hblock
      rcases hblock with hfirst | htail
      · refine ⟨p, ps.takeWhile (fun q =>
            decide (phaseThreshold α p < q.active.card)), hfirst, ?_⟩
        omega
      · exact greedyRawBlocks_shape α
          (ps.dropWhile (fun q =>
            decide (phaseThreshold α p < q.active.card))) block htail
termination_by phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := ps)
    (fun q : Phase n profile =>
      decide (phaseThreshold α p < q.active.card))).length_le
  simp_all only [List.length_cons]
  omega

/-- If every eligible block head lies above its own threshold, then every
member of every greedy block lies above that head's threshold. -/
theorem greedyRawBlocks_above_threshold {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile))
    (hhead : ∀ p ∈ phases, 2 < p.active.card →
      phaseThreshold α p < p.active.card)
    (block : List (Phase n profile))
    (hblock : block ∈ (greedyRawBlocks α phases).1) :
    ∃ first rest, block = first :: rest ∧
      ∀ q ∈ block, phaseThreshold α first < q.active.card := by
  cases phases with
  | nil => simp [greedyRawBlocks] at hblock
  | cons p ps =>
    rw [greedyRawBlocks] at hblock
    split at hblock
    next hsmall => simp at hblock
    next hlarge =>
      simp only [List.mem_cons] at hblock
      rcases hblock with hfirst | htail
      · let pred := fun q : Phase n profile =>
          decide (phaseThreshold α p < q.active.card)
        let pre := ps.takeWhile pred
        have hEq : block = p :: pre := by
          simpa [pred, pre] using hfirst
        refine ⟨p, pre, hEq, ?_⟩
        intro q hq
        rw [hEq] at hq
        simp only [List.mem_cons] at hq
        rcases hq with hqp | hq
        · subst q
          exact hhead p (by simp) (by omega)
        · exact of_decide_eq_true (mem_takeWhile_true pred ps hq)
      · have hsub := List.dropWhile_sublist (l := ps)
          (fun q : Phase n profile =>
            decide (phaseThreshold α p < q.active.card))
        apply greedyRawBlocks_above_threshold α _ _ block htail
        intro q hq hqcard
        exact hhead q (by
          apply List.mem_cons_of_mem
          exact hsub.subset hq) hqcard
termination_by phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := ps)
    (fun q : Phase n profile =>
      decide (phaseThreshold α p < q.active.card))).length_le
  simp_all only [List.length_cons]
  omega

/-- If the raw algorithm returns a terminal suffix, its first phase has at
most two active goods. -/
theorem greedyRawTerminal_head_small {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile))
    {p : Phase n profile} {ps : List (Phase n profile)}
    (hterm : (greedyRawBlocks α phases).2 = p :: ps) :
    p.active.card ≤ 2 := by
  cases phases with
  | nil => simp [greedyRawBlocks] at hterm
  | cons first rest =>
    rw [greedyRawBlocks] at hterm
    split at hterm
    next hsmall =>
      injection hterm with hp hps
      simpa [hp] using hsmall
    next hlarge =>
      exact greedyRawTerminal_head_small α
        (rest.dropWhile (fun q =>
          decide (phaseThreshold α first < q.active.card))) hterm
termination_by phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := rest)
    (fun q : Phase n profile =>
      decide (phaseThreshold α first < q.active.card))).length_le
  simp_all only [List.length_cons]
  omega

/-! ## Turning raw blocks into survivor blocks -/

def rawTerminalCarrier {n : ℕ} {profile : Profile n} (α : ℝ)
    (phases : List (Phase n profile)) : Finset (Fin n) :=
  match (greedyRawBlocks α phases).2 with
  | [] => ∅
  | p :: _ => p.active

lemma rawTerminalCarrier_card_le_two {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile)) :
    (rawTerminalCarrier α phases).card ≤ 2 := by
  unfold rawTerminalCarrier
  split
  · simp
  next p ps heq =>
    exact greedyRawTerminal_head_small α phases heq

lemma rawTerminal_active_subset_carrier {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile))
    (hpair : phases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active))
    (p : Phase n profile) (hp : p ∈ (greedyRawBlocks α phases).2) :
    p.active ⊆ rawTerminalCarrier α phases := by
  have htermPair : (greedyRawBlocks α phases).2.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
    List.Pairwise.sublist (greedyRawTerminal_sublist α phases) hpair
  unfold rawTerminalCarrier
  generalize hterm : (greedyRawBlocks α phases).2 = terminal at hp htermPair ⊢
  cases terminal with
  | nil => simp at hp
  | cons first rest =>
      simp only
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact fun _ h => h
      · exact (List.pairwise_cons.mp htermPair).1 p hp |>.subset

lemma candidateSize_anti {n : ℕ} {α lambda₁ lambda₂ : ℝ}
    (hα : 0 ≤ α) (hlambda : lambda₁ ≤ lambda₂) :
    candidateSize n α lambda₂ ≤ candidateSize n α lambda₁ := by
  unfold candidateSize
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Every raw greedy block has a last active set large enough to be its
survivor, and the concrete load-good event supplies the demand field required
by `SurvivorBlock`. -/
theorem exists_survivorBlock_of_raw {n : ℕ} {profile : Profile n}
    {lambdaZero : ℝ}
    (hgood : ConcretePhaseLoadGood profile lambdaZero)
    (phases : List (Phase n profile))
    (hphasesSub : phases.Sublist (run profile).phases)
    (hpair : phases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active))
    (hratio : ∀ p ∈ phases, lambdaZero ≤ phaseRatio p)
    (hthreshold : ∀ p ∈ phases, 2 < p.active.card →
      phaseThreshold alphaZero p < p.active.card)
    (block : List (Phase n profile))
    (hblock : block ∈ (greedyRawBlocks alphaZero phases).1) :
    ∃ certified : SurvivorBlock n profile etaZero,
      certified.phases = block := by
  obtain ⟨first, rest, hblockEq, habove⟩ :=
    greedyRawBlocks_above_threshold alphaZero phases hthreshold block hblock
  have hblockNe : block ≠ [] := by simp [hblockEq]
  let last : Phase n profile := block.getLast hblockNe
  have hlastMem : last ∈ block := List.getLast_mem hblockNe
  have hblockSubPhases := greedyRawBlock_sublist alphaZero phases block hblock
  have hblockSubRun : block.Sublist (run profile).phases :=
    hblockSubPhases.trans hphasesSub
  have hblockPairStrict : block.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
    List.Pairwise.sublist hblockSubPhases hpair
  have hblockPair : block.Pairwise
      (fun earlier later => later.active ⊆ earlier.active) :=
    hblockPairStrict.imp (fun h => h.subset)
  letI : IsRefl (Phase n profile)
      (fun earlier later => later.active ⊆ earlier.active) :=
    ⟨fun _ => fun _ h => h⟩
  have hsurvivor : ∀ p ∈ block, last.active ⊆ p.active := by
    intro p hp
    exact hblockPair.rel_getLast hp
  have hlastLarge : phaseThreshold alphaZero first < last.active.card :=
    habove last hlastMem
  refine ⟨{
    phases := block
    survivor := last.active
    survivor_nonempty := last.active_nonempty
    phases_sublist := hblockSubRun
    demand := ?_ }, rfl⟩
  intro p hp
  have hpPhases : p ∈ phases := hblockSubPhases.subset hp
  have hpRun : p ∈ (run profile).phases := hphasesSub.subset hpPhases
  have hfirstPair := List.pairwise_cons.mp (hblockEq ▸ hblockPairStrict)
  have hfirstRatio : phaseRatio first ≤ phaseRatio p := by
    rw [hblockEq] at hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_rfl
    · exact inverseCard_mono (hfirstPair.1 p hp).subset
  have hcand : candidateSize n alphaZero (phaseRatio p) ≤
      candidateSize n alphaZero (phaseRatio first) :=
    candidateSize_anti alphaZero_pos.le hfirstRatio
  have hlarge : 2 * candidateSize n alphaZero (phaseRatio p) ≤
      last.active.card := by
    have htwice : 2 * candidateSize n alphaZero (phaseRatio p) ≤
        2 * candidateSize n alphaZero (phaseRatio first) :=
      Nat.mul_le_mul_left 2 hcand
    exact htwice.trans (Nat.le_of_lt hlastLarge)
  exact concretePhaseLoadGood_demand hgood p hpRun
    (hratio p hpPhases) last.active (hsurvivor p (by
      simpa [hblockEq] using hp)) hlarge

/-! ## The recurrence between consecutive greedy blocks -/

def RawBlockTransition {n : ℕ} {profile : Profile n} (α : ℝ)
    (earlier later : List (Phase n profile)) : Prop :=
  ∃ first earlierRest next laterRest,
    earlier = first :: earlierRest ∧ later = next :: laterRest ∧
      next.active.card ≤ phaseThreshold α first

lemma greedyRawBlocks_first {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases block : List (Phase n profile))
    (blocks : List (List (Phase n profile)))
    (heq : (greedyRawBlocks α phases).1 = block :: blocks) :
    ∃ first rest blockRest,
      phases = first :: rest ∧ block = first :: blockRest ∧
        2 < first.active.card := by
  cases phases with
  | nil => simp [greedyRawBlocks] at heq
  | cons first rest =>
    rw [greedyRawBlocks] at heq
    split at heq
    next hsmall => simp at heq
    next hlarge =>
      injection heq with hblock hblocks
      refine ⟨first, rest, rest.takeWhile (fun q =>
        decide (phaseThreshold α first < q.active.card)), rfl, ?_, by omega⟩
      exact hblock.symm

theorem greedyRawBlocks_chain {n : ℕ} {profile : Profile n}
    (α : ℝ) (phases : List (Phase n profile)) :
    (greedyRawBlocks α phases).1.Chain' (RawBlockTransition α) := by
  cases phases with
  | nil => simp [greedyRawBlocks]
  | cons first rest =>
    rw [greedyRawBlocks]
    split
    next hsmall => simp
    next hlarge =>
      dsimp only
      let pred := fun q : Phase n profile =>
        decide (phaseThreshold α first < q.active.card)
      let pre := rest.takeWhile pred
      let remaining := rest.dropWhile pred
      have ih := greedyRawBlocks_chain α remaining
      generalize htail : (greedyRawBlocks α remaining).1 = tailBlocks at ih
      change ((first :: pre) :: tailBlocks).Chain'
        (RawBlockTransition α)
      cases tailBlocks with
      | nil => simp
      | cons nextBlock more =>
          rw [List.chain'_cons]
          refine ⟨?_, ih⟩
          obtain ⟨next, nextRest, nextBlockRest,
            hremaining, hnextBlock, hnextCard⟩ :=
            greedyRawBlocks_first α remaining nextBlock more htail
          have hnotPred : ¬ pred next = true := by
            apply head_dropWhile_false pred rest
            simpa [remaining] using hremaining
          have hcard : next.active.card ≤ phaseThreshold α first := by
            simpa [pred] using hnotPred
          refine ⟨first, pre, next, nextBlockRest, rfl, hnextBlock, hcard⟩
termination_by phases.length
decreasing_by
  have hlen := (List.dropWhile_sublist (l := tail)
    (fun q : Phase n profile =>
      decide (phaseThreshold α head < q.active.card))).length_le
  simp_all only [List.length_cons]
  omega

/-- Scale attached to the first phase of a nonempty raw block. -/
def rawBlockScale {n : ℕ} {profile : Profile n} (α : ℝ)
    (block : List (Phase n profile)) : ℝ :=
  match block with
  | [] => 0
  | first :: _ => α * phaseRatio first / 2

lemma rawTransition_scale {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {lambdaZero : ℝ}
    (hconditions : PhaseLambdaConditions lambdaZero)
    {earlier later : List (Phase n profile)}
    (hearlier : ∃ first rest, earlier = first :: rest ∧
      lambdaZero ≤ phaseRatio first)
    (hlater : ∃ next rest, later = next :: rest ∧
      2 < next.active.card)
    (htransition : RawBlockTransition alphaZero earlier later) :
    Real.exp (rawBlockScale alphaZero earlier) ≤
      rawBlockScale alphaZero later := by
  obtain ⟨first, earlierRest, hearlierEq, hfirstLambda⟩ := hearlier
  obtain ⟨next, laterRest, hlaterEq, hnextLarge⟩ := hlater
  obtain ⟨first', earlierRest', next', laterRest',
    hearlierEq', hlaterEq', hnextBound⟩ := htransition
  have hfirst : first' = first := by
    have hheads : (first :: earlierRest).head? =
        (first' :: earlierRest').head? := by
      rw [← hearlierEq, ← hearlierEq']
    simpa using hheads.symm
  have hnext : next' = next := by
    have hheads : (next :: laterRest).head? =
        (next' :: laterRest').head? := by
      rw [← hlaterEq, ← hlaterEq']
    simpa using hheads.symm
  subst first'
  subst next'
  have hphaseConstant :=
    (hconditions.2 (phaseRatio first) hfirstLambda).2.2.2
  have hbase : 1 ≤ candidateBase n alphaZero (phaseRatio first) := by
    by_cases h : 1 ≤ candidateBase n alphaZero (phaseRatio first)
    · exact h
    · have hbaseLe : candidateBase n alphaZero (phaseRatio first) ≤ 1 :=
        (lt_of_not_ge h).le
      have htwo := nextActive_le_two_of_base_le_one hnextBound hbaseLe
      omega
  simpa [rawBlockScale, hearlierEq, hlaterEq] using
    activeSize_recurrence_gives_exp_scale hn
      (Finset.card_pos.mpr next.active_nonempty) alphaZero_pos
      hnextBound hbase hphaseConstant

lemma chain_imp_of_mem {γ : Type*} {R S : γ → γ → Prop}
    {P : γ → Prop} {xs : List γ}
    (hchain : xs.Chain' R) (hall : ∀ x ∈ xs, P x)
    (himp : ∀ a b, P a → P b → R a b → S a b) :
    xs.Chain' S := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases xs with
      | nil => simp
      | cons b xs =>
          rw [List.chain'_cons] at hchain ⊢
          refine ⟨himp a b (hall a (by simp)) (hall b (by simp)) hchain.1, ?_⟩
          apply ih hchain.2
          intro x hx
          exact hall x (by simp [hx])

/-- Every raw block starts at an eligible phase of the input list. -/
lemma rawBlock_start_data {n : ℕ} {profile : Profile n}
    (α : ℝ) {lambdaZero : ℝ}
    (phases : List (Phase n profile))
    (hratio : ∀ p ∈ phases, lambdaZero ≤ phaseRatio p)
    (block : List (Phase n profile))
    (hblock : block ∈ (greedyRawBlocks α phases).1) :
    ∃ first rest, block = first :: rest ∧
      lambdaZero ≤ phaseRatio first ∧ 2 < first.active.card := by
  obtain ⟨first, rest, hEq, hlarge⟩ :=
    greedyRawBlocks_shape α phases block hblock
  refine ⟨first, rest, hEq, ?_, hlarge⟩
  apply hratio first
  exact (greedyRawBlock_sublist α phases block hblock).subset (by simp [hEq])

theorem rawBlockScales_chain {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {lambdaZero : ℝ}
    (hconditions : PhaseLambdaConditions lambdaZero)
    (phases : List (Phase n profile))
    (hratio : ∀ p ∈ phases, lambdaZero ≤ phaseRatio p) :
    ((greedyRawBlocks alphaZero phases).1.map
      (rawBlockScale alphaZero)).Chain'
        (fun earlier later => Real.exp earlier ≤ later) := by
  rw [List.chain'_map]
  apply chain_imp_of_mem (greedyRawBlocks_chain alphaZero phases)
    (P := fun block => ∃ first rest, block = first :: rest ∧
      lambdaZero ≤ phaseRatio first ∧ 2 < first.active.card)
  · intro block hblock
    exact rawBlock_start_data alphaZero phases hratio block hblock
  · intro earlier later hearlier hlater htransition
    obtain ⟨first, rest, hEq, hLambda, hlarge⟩ := hearlier
    obtain ⟨next, nextRest, hNextEq, hNextLambda, hNextLarge⟩ := hlater
    exact rawTransition_scale hn hconditions
      ⟨first, rest, hEq, hLambda⟩
      ⟨next, nextRest, hNextEq, hNextLarge⟩ htransition

lemma rawTransition_below_log_target {n : ℕ} {profile : Profile n}
    (hn : 0 < n) {earlier later : List (Phase n profile)}
    (hearlier : ∃ first rest, earlier = first :: rest)
    (hlater : ∃ next rest, later = next :: rest ∧
      2 < next.active.card)
    (htransition : RawBlockTransition alphaZero earlier later) :
    rawBlockScale alphaZero earlier < Real.log (n : ℝ) / 2 := by
  obtain ⟨first, earlierRest, hearlierEq⟩ := hearlier
  obtain ⟨next, laterRest, hlaterEq, hnextLarge⟩ := hlater
  obtain ⟨first', earlierRest', next', laterRest',
    hearlierEq', hlaterEq', hnextBound⟩ := htransition
  have hfirst : first' = first := by
    have hheads : (first :: earlierRest).head? =
        (first' :: earlierRest').head? := by
      rw [← hearlierEq, ← hearlierEq']
    simpa using hheads.symm
  have hnext : next' = next := by
    have hheads : (next :: laterRest).head? =
        (next' :: laterRest').head? := by
      rw [← hlaterEq, ← hlaterEq']
    simpa using hheads.symm
  subst first'
  subst next'
  rw [hearlierEq]
  change alphaZero * phaseRatio first / 2 < Real.log (n : ℝ) / 2
  by_contra hnot
  have hthreshold : Real.log (n : ℝ) / 2 ≤
      alphaZero * phaseRatio first / 2 := le_of_not_gt hnot
  have hbase := candidateBase_le_one_of_log_threshold hn hthreshold
  have htwo := nextActive_le_two_of_base_le_one hnextBound hbase
  omega

theorem rawBlockScales_below_chain {n : ℕ} {profile : Profile n}
    (hn : 0 < n) (phases : List (Phase n profile)) :
    (greedyRawBlocks alphaZero phases).1.Chain'
      (fun earlier _later =>
        rawBlockScale alphaZero earlier < Real.log (n : ℝ) / 2) := by
  apply chain_imp_of_mem (greedyRawBlocks_chain alphaZero phases)
    (P := fun block => ∃ first rest, block = first :: rest ∧
      2 < first.active.card)
  · intro block hblock
    exact greedyRawBlocks_shape alphaZero phases block hblock
  · intro earlier later hearlier hlater htransition
    exact rawTransition_below_log_target hn
      ⟨hearlier.choose, hearlier.choose_spec.choose,
        hearlier.choose_spec.choose_spec.1⟩ hlater htransition

/-- Extend the finite block-scale list to a total sequence, using `fallback`
outside its range. -/
def extendScale (fallback : ℝ) (values : List ℝ) (k : ℕ) : ℝ :=
  if h : k < values.length then values[k] else fallback

lemma extendScale_eq_getElem (fallback : ℝ) (values : List ℝ)
    {k : ℕ} (hk : k < values.length) :
    extendScale fallback values k = values[k] := by
  simp [extendScale, hk]

lemma extendScale_step (fallback : ℝ) (values : List ℝ)
    (hchain : values.Chain' (fun earlier later => Real.exp earlier ≤ later))
    (k : ℕ) (hk : k + 1 < values.length) :
    Real.exp (extendScale fallback values k) ≤
      extendScale fallback values (k + 1) := by
  rw [extendScale_eq_getElem fallback values (by omega),
    extendScale_eq_getElem fallback values hk]
  have hrel := (List.chain'_iff_get.mp hchain) k (by omega)
  simpa using hrel

lemma extendScale_below (fallback : ℝ) (values : List ℝ)
    (hchain : values.Chain'
      (fun earlier _later => earlier < Real.log (n : ℝ) / 2))
    (k : ℕ) (hk : k + 1 < values.length) :
    extendScale fallback values k < Real.log (n : ℝ) / 2 := by
  rw [extendScale_eq_getElem fallback values (by omega)]
  have hrel := (List.chain'_iff_get.mp hchain) k (by omega)
  simpa using hrel

/-! ## Building the concrete `PhaseCertificate` -/

lemma exists_list_map_eq_of_forall_mem {γ δ : Type*}
    (f : δ → γ) (xs : List γ)
    (hexists : ∀ x ∈ xs, ∃ y : δ, f y = x) :
    ∃ ys : List δ, ys.map f = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy⟩ := hexists x (by simp)
      obtain ⟨ys, hys⟩ := ih (by
        intro z hz
        exact hexists z (by simp [hz]))
      refine ⟨y :: ys, ?_⟩
      simp [hy, hys]

theorem exists_phaseCertificate_of_concreteLoadGood
    {n : ℕ} (profile : Profile n) (hn : 0 < n)
    (hgood : ConcretePhaseLoadGood profile phaseLambdaZero) :
    Nonempty (PhaseCertificate n profile etaZero phaseLambdaZero
        (alphaZero * phaseLambdaZero / 2)
        (Real.log (n : ℝ) / 2)) := by
  let allPhases := (run profile).phases
  let initial := initialPhases phaseLambdaZero allPhases
  let middle := postInitialPhases phaseLambdaZero allPhases
  let raw := (greedyRawBlocks alphaZero middle).1
  let terminal := (greedyRawBlocks alphaZero middle).2
  have hallPair : allPhases.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
    run_phases_pairwise profile
  have hinitialSub : initial.Sublist allPhases := by
    exact List.takeWhile_sublist _
  have hmiddleSub : middle.Sublist allPhases := by
    exact List.dropWhile_sublist _
  have hmiddlePair : middle.Pairwise
      (fun earlier later => later.active ⊂ earlier.active) :=
    List.Pairwise.sublist hmiddleSub hallPair
  have hmiddleRatio : ∀ p ∈ middle,
      phaseLambdaZero ≤ phaseRatio p := by
    intro p hp
    exact (postInitialPhases_ratio_gt phaseLambdaZero allPhases
      hallPair hp).le
  have hthreshold : ∀ p ∈ middle, 2 < p.active.card →
      phaseThreshold alphaZero p < p.active.card := by
    intro p hp hpLarge
    exact twice_candidateSize_lt_activeCard hpLarge phaseLambdaZero_spec
      (hmiddleRatio p hp)
  have hrawCertified : ∀ block ∈ raw,
      ∃ certified : SurvivorBlock n profile etaZero,
        certified.phases = block := by
    intro block hblock
    exact exists_survivorBlock_of_raw hgood middle
      (by simpa [allPhases] using hmiddleSub) hmiddlePair
      hmiddleRatio hthreshold block hblock
  obtain ⟨certified, hcertified⟩ :=
    exists_list_map_eq_of_forall_mem
      (fun block : SurvivorBlock n profile etaZero => block.phases)
      raw hrawCertified
  have hcertLength : certified.length = raw.length := by
    have hlen := congrArg List.length hcertified
    simpa using hlen
  let values : List ℝ := raw.map (rawBlockScale alphaZero)
  let uZero : ℝ := alphaZero * phaseLambdaZero / 2
  let scale : ℕ → ℝ := extendScale uZero values
  have hscaleStart : uZero ≤ scale 0 := by
    cases hraw : raw with
    | nil => simp [scale, values, extendScale, hraw]
    | cons block blocks =>
        have hblockMem : block ∈ raw := by simp [hraw]
        obtain ⟨first, rest, hEq, hLambda, hlarge⟩ :=
          rawBlock_start_data alphaZero middle hmiddleRatio block hblockMem
        have hscaled := mul_le_mul_of_nonneg_left hLambda alphaZero_pos.le
        simpa [scale, values, extendScale, hraw, rawBlockScale, hEq,
          uZero] using (div_le_div_of_nonneg_right hscaled (by norm_num : (0 : ℝ) ≤ 2))
  have hvaluesChain : values.Chain'
      (fun earlier later => Real.exp earlier ≤ later) := by
    exact rawBlockScales_chain hn phaseLambdaZero_spec middle hmiddleRatio
  have hscaleStep : ∀ k, k + 1 < certified.length →
      Real.exp (scale k) ≤ scale (k + 1) := by
    intro k hk
    apply extendScale_step uZero values hvaluesChain k
    simpa [values, hcertLength] using hk
  have hbelowChain : raw.Chain'
      (fun earlier _later =>
        rawBlockScale alphaZero earlier < Real.log (n : ℝ) / 2) :=
    rawBlockScales_below_chain hn middle
  have hvaluesBelow : values.Chain'
      (fun earlier _later => earlier < Real.log (n : ℝ) / 2) := by
    rw [List.chain'_map]
    exact hbelowChain
  have hscaleBelow : ∀ k, k + 1 < certified.length →
      scale k < Real.log (n : ℝ) / 2 := by
    intro k hk
    apply extendScale_below uZero values hvaluesBelow k
    simpa [values, hcertLength] using hk
  have hterminalSubMiddle : terminal.Sublist middle := by
    exact greedyRawTerminal_sublist alphaZero middle
  have hterminalSubRun : terminal.Sublist (run profile).phases :=
    hterminalSubMiddle.trans hmiddleSub
  have hdecompMiddle : raw.flatten ++ terminal = middle :=
    greedyRawBlocks_decomposition alphaZero middle
  have hdecompAll : initial ++ middle = allPhases :=
    initial_append_postInitial phaseLambdaZero allPhases
  let carrier := rawTerminalCarrier alphaZero middle
  refine ⟨{
    initial := initial
    blocks := certified
    terminal := terminal
    decomposition := ?_
    initial_sublist := hinitialSub
    initial_ratio := ?_
    terminalCarrier := carrier
    terminalCarrier_card := ?_
    terminal_sublist := hterminalSubRun
    terminal_active := ?_
    scale := scale
    scale_start := hscaleStart
    scale_step := hscaleStep
    scale_below := hscaleBelow }⟩
  · change allPhases = initial ++
      (certified.map SurvivorBlock.phases).flatten ++ terminal
    have hcertified' : certified.map SurvivorBlock.phases = raw := by
      simpa using hcertified
    rw [hcertified', List.append_assoc, hdecompMiddle]
    exact hdecompAll.symm
  · intro p hp
    exact initialPhases_ratio_le phaseLambdaZero allPhases hp
  · exact rawTerminalCarrier_card_le_two alphaZero middle
  · intro p hp
    exact rawTerminal_active_subset_carrier alphaZero middle
      hmiddlePair p hp

/-- Step 9's concrete deterministic conclusion: the simultaneous underload
event on the actual PS trace implies the full iterated-log eating bound. -/
theorem concrete_eatingIntegral_le {n : ℕ} (profile : Profile n) (hn : 0 < n)
    (hgood : ConcretePhaseLoadGood profile phaseLambdaZero) :
    eatingIntegral (run profile) ≤
      phaseLambdaZero + (8 / etaZero) *
        ((exponentialHeight (alphaZero * phaseLambdaZero / 2)
          (Real.log (n : ℝ) / 2) : ℝ) + 1) + 2 := by
  obtain ⟨cert⟩ :=
    exists_phaseCertificate_of_concreteLoadGood profile hn hgood
  exact eatingIntegral_le_of_phaseCertificate hn etaZero_pos
    phaseLambdaZero_pos.le cert

/-- The concrete shifted log-star normalization generated by the phase
recurrence. -/
def psLogStar (n : ℕ) : ℝ :=
  exponentialHeight (alphaZero * phaseLambdaZero / 2)
    (Real.log (n : ℝ) / 2)

lemma psLogStar_nonneg (n : ℕ) : 0 ≤ psLogStar n := by
  exact Nat.cast_nonneg _

/-- One absolute multiplier absorbing the initial interval, every survivor
block, and the terminal interval. -/
def concretePhaseConstant : ℝ :=
  phaseLambdaZero + 2 + 8 / etaZero

lemma concretePhaseConstant_pos : 0 < concretePhaseConstant := by
  unfold concretePhaseConstant
  have heta : 0 < 8 / etaZero := div_pos (by norm_num) etaZero_pos
  linarith [phaseLambdaZero_pos]

/-- Proposition `logstar-integral` in the exact `C(1+logStar n)` form used by
the main theorem assembly. -/
theorem concrete_eatingIntegral_le_logStar {n : ℕ}
    (profile : Profile n) (hn : 0 < n)
    (hgood : ConcretePhaseLoadGood profile phaseLambdaZero) :
    eatingIntegral (run profile) ≤
      concretePhaseConstant * (1 + psLogStar n) := by
  have hbound := concrete_eatingIntegral_le profile hn hgood
  have hL : 0 ≤ phaseLambdaZero + 2 := by
    linarith [phaseLambdaZero_pos]
  have hstar := psLogStar_nonneg n
  have hproduct : 0 ≤ (phaseLambdaZero + 2) * psLogStar n :=
    mul_nonneg hL hstar
  unfold concretePhaseConstant psLogStar
  nlinarith


end ProbabilisticSerial.PhaseAdapter
