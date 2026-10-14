import PSProcess
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Replica markets from the verified deterministic eating process

There are `m*q` independently ranked agents and `m` types of capacity `q`.
We implement capacity by `q` ordered unit copies of each type. Every agent
places all copies of a type consecutively, in the same copy order. Grouping
the resulting unit-copy allocation gives a feasible replica allocation.
Ranks and the probability sample in this file are over types, not copies.

The uniform-copy concentration law does not apply to the lifted preferences:
their blocks are deliberately dependent. Replica concentration therefore
requires its own type-level revelation argument.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaPS

open UniformPermutation PSProcess

abbrev Profile (m q : ℕ) := Fin (m * q) → PreferenceOrder m

def profileSample (m q : ℕ) : Finset (Profile m q) :=
  UniformProduct.productSample (preferenceSample m) (m * q)

lemma profileSample_nonempty (m q : ℕ) : (profileSample m q).Nonempty :=
  UniformProduct.productSample_nonempty (preferenceSample_nonempty m) (m * q)

def copyOf {m q : ℕ} (g : Fin m) (k : Fin q) : Fin (m * q) :=
  finProdFinEquiv (g, k)

def typeOf {m q : ℕ} (c : Fin (m * q)) : Fin m :=
  (finProdFinEquiv.symm c).1

@[simp] lemma typeOf_copyOf {m q : ℕ} (g : Fin m) (k : Fin q) :
    typeOf (copyOf g k) = g := by
  simp [typeOf, copyOf]

def liftPreference {m q : ℕ} (σ : PreferenceOrder m) : PreferenceOrder (m * q) :=
  (finProdFinEquiv.symm.trans (Equiv.prodCongr σ (Equiv.refl (Fin q)))).trans
    finProdFinEquiv

@[simp] lemma liftPreference_apply {m q : ℕ} (σ : PreferenceOrder m)
    (g : Fin m) (k : Fin q) :
    liftPreference σ (copyOf g k) = copyOf (σ g) k := by
  simp [liftPreference, copyOf]

@[simp] lemma liftPreference_symm_apply {m q : ℕ} (σ : PreferenceOrder m)
    (g : Fin m) (k : Fin q) :
    (liftPreference σ).symm (copyOf g k) = copyOf (σ.symm g) k := by
  apply (liftPreference σ).injective
  simp

lemma rankOf_copy {m q : ℕ} (σ : PreferenceOrder m) (g : Fin m) (k : Fin q) :
    rankOf (liftPreference σ) (copyOf g k) =
      k.val + q * (σ.symm g).val + 1 := by
  unfold rankOf
  rw [liftPreference_symm_apply]
  rfl

lemma favorite_rank_le {m : ℕ} (σ : PreferenceOrder m) (S : Finset (Fin m))
    (hS : S.Nonempty) (g : Fin m) (hg : g ∈ S) :
    rankOf σ (favorite σ S hS) ≤ rankOf σ g := by
  have hg' : σ.symm g ∈ preimageFinset σ S := by
    simp [preimageFinset, hg]
  have h := Finset.min'_le (preimageFinset σ S) (σ.symm g) hg'
  simp only [rankOf, favorite, Equiv.symm_apply_apply]
  exact Nat.add_le_add_right h 1

/-- At every exhaustion phase the preferred surviving copy has exactly the
preferred surviving type. This justifies using the existing unit-copy eating
algorithm to implement the replica mechanism, with additional internal copy
exhaustions that do not change the type preference order. -/
theorem favorite_type {m q : ℕ} (σ : PreferenceOrder m)
    (S : Finset (Fin (m * q))) (hS : S.Nonempty) :
    typeOf (favorite (liftPreference σ) S hS) =
      favorite σ (S.image typeOf) (hS.image typeOf) := by
  let c := favorite (liftPreference σ) S hS
  let t := favorite σ (S.image typeOf) (hS.image typeOf)
  have hcS : c ∈ S := favorite_mem _ S hS
  have htS : t ∈ S.image typeOf := favorite_mem σ _ _
  obtain ⟨d, hdS, hdt⟩ := Finset.mem_image.mp htS
  obtain ⟨⟨g, k⟩, hc⟩ := finProdFinEquiv.surjective c
  obtain ⟨⟨g', k'⟩, hd⟩ := finProdFinEquiv.surjective d
  change copyOf g k = c at hc
  change copyOf g' k' = d at hd
  have hg't : g' = t := by simpa [← hd] using hdt
  have hmin := favorite_rank_le (liftPreference σ) S hS d hdS
  change rankOf (liftPreference σ) c ≤ rankOf (liftPreference σ) d at hmin
  rw [← hc, ← hd, rankOf_copy, rankOf_copy, hg't] at hmin
  have hpos : (σ.symm g).val ≤ (σ.symm t).val := by
    by_contra hnot
    have hgap : (σ.symm t).val + 1 ≤ (σ.symm g).val := by omega
    have hmul := Nat.mul_le_mul_left q hgap
    nlinarith [k'.isLt]
  have hgS : g ∈ S.image typeOf := by
    have h : typeOf c ∈ S.image (typeOf (m := m) (q := q)) :=
      Finset.mem_image.mpr ⟨c, hcS, rfl⟩
    simpa [← hc] using h
  have hreverse := favorite_rank_le σ (S.image typeOf) (hS.image typeOf) g hgS
  change rankOf σ t ≤ rankOf σ g at hreverse
  have heq : (σ.symm g).val = (σ.symm t).val := by
    dsimp [rankOf] at hreverse
    omega
  have hgt : g = t := σ.symm.injective (Fin.ext heq)
  change typeOf c = t
  rw [← hc, typeOf_copyOf, hgt]

def liftedProfile {m q : ℕ} (profile : Profile m q) : PSProcess.Profile (m * q) :=
  fun i => liftPreference (profile i)

def allocation {m q : ℕ} (profile : Profile m q) (i : Fin (m * q)) (g : Fin m) : ℝ :=
  ∑ k : Fin q, PSProcess.allocation (run (liftedProfile profile)) i (copyOf g k)

theorem allocation_nonneg {m q : ℕ} (profile : Profile m q)
    (i : Fin (m * q)) (g : Fin m) : 0 ≤ allocation profile i g := by
  apply Finset.sum_nonneg
  intro k hk
  exact run_allocation_nonneg (liftedProfile profile) i (copyOf g k)

lemma sum_copies {m q : ℕ} (F : Fin (m * q) → ℝ) :
    (∑ g : Fin m, ∑ k : Fin q, F (copyOf g k)) = ∑ c : Fin (m * q), F c := by
  calc
    _ = ∑ pair : Fin m × Fin q, F (finProdFinEquiv pair) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

theorem allocation_agent_sum {m q : ℕ} (profile : Profile m q)
    (hm : 0 < m) (hq : 0 < q) (i : Fin (m * q)) :
    (∑ g : Fin m, allocation profile i g) = 1 := by
  unfold allocation
  rw [sum_copies]
  exact run_allocation_agent_sum (liftedProfile profile) (Nat.mul_pos hm hq) i

theorem allocation_type_sum {m q : ℕ} (profile : Profile m q) (g : Fin m) :
    (∑ i : Fin (m * q), allocation profile i g) = q := by
  unfold allocation
  rw [Finset.sum_comm]
  simp_rw [run_allocation_good_sum]
  simp

def agentRank {m q : ℕ} (profile : Profile m q) (i : Fin (m * q)) : ℝ :=
  ∑ g : Fin m, (rankOf (profile i) g : ℝ) * allocation profile i g

def averageRank {m q : ℕ} (profile : Profile m q) : ℝ :=
  𝔼 i : Fin (m * q), agentRank profile i

def expectedPS (m q : ℕ) : ℝ :=
  𝔼 profile ∈ profileSample m q, averageRank profile

theorem agentRank_bounds {m q : ℕ} (profile : Profile m q)
    (hm : 0 < m) (hq : 0 < q) (i : Fin (m * q)) :
    1 ≤ agentRank profile i ∧ agentRank profile i ≤ m := by
  have hsum := allocation_agent_sum profile hm hq i
  constructor
  · calc
      1 = ∑ g : Fin m, (1 : ℝ) * allocation profile i g := by simpa using hsum.symm
      _ ≤ agentRank profile i := by
        apply Finset.sum_le_sum
        intro g hg
        apply mul_le_mul_of_nonneg_right _ (allocation_nonneg profile i g)
        have h : 1 ≤ rankOf (profile i) g := by simp [rankOf]
        exact_mod_cast h
  · calc
      agentRank profile i ≤ ∑ g : Fin m, (m : ℝ) * allocation profile i g := by
        apply Finset.sum_le_sum
        intro g hg
        apply mul_le_mul_of_nonneg_right _ (allocation_nonneg profile i g)
        exact_mod_cast rankOf_le_marketSize (profile i) g
      _ = m := by rw [← Finset.mul_sum, hsum, mul_one]

theorem averageRank_bounds {m q : ℕ} (profile : Profile m q)
    (hm : 0 < m) (hq : 0 < q) :
    1 ≤ averageRank profile ∧ averageRank profile ≤ m := by
  have hs : (Finset.univ : Finset (Fin (m * q))).Nonempty := by
    exact ⟨⟨0, Nat.mul_pos hm hq⟩, Finset.mem_univ _⟩
  constructor
  · calc
      (1 : ℝ) = 𝔼 _i : Fin (m * q), (1 : ℝ) := (Finset.expect_const hs 1).symm
      _ ≤ averageRank profile := Finset.expect_le_expect (fun i _ =>
        (agentRank_bounds profile hm hq i).1)
  · calc
      averageRank profile ≤ 𝔼 _i : Fin (m * q), (m : ℝ) :=
        Finset.expect_le_expect (fun i _ => (agentRank_bounds profile hm hq i).2)
      _ = m := Finset.expect_const hs _

theorem expectedPS_bounds (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    1 ≤ expectedPS m q ∧ expectedPS m q ≤ m := by
  constructor
  · calc
      (1 : ℝ) = 𝔼 _profile ∈ profileSample m q, (1 : ℝ) :=
        (Finset.expect_const (profileSample_nonempty m q) 1).symm
      _ ≤ expectedPS m q := Finset.expect_le_expect (fun profile _ =>
        (averageRank_bounds profile hm hq).1)
  · calc
      expectedPS m q ≤ 𝔼 _profile ∈ profileSample m q, (m : ℝ) :=
        Finset.expect_le_expect (fun profile _ => (averageRank_bounds profile hm hq).2)
      _ = m := Finset.expect_const (profileSample_nonempty m q) _

theorem expectedPS_one_type (q : ℕ) (hq : 0 < q) : expectedPS 1 q = 1 := by
  have h := expectedPS_bounds 1 q (by omega) hq
  norm_num at h
  exact le_antisymm h.2 h.1

end ProbabilisticSerial.ReplicaPS
