import ReplicaPS

/-!
# Random priority in a replica market

This is serial dictatorship on remaining copies, with the same type-block
preferences used by the replica PS model. The statistic records original
type ranks. A uniform priority permutation is independent of the uniform
type preference profile. No Gamma-clock formula is built into the definition.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.ReplicaRP

open UniformPermutation PSProcess ReplicaPS

def serialTypeRankSum {m q : ℕ} :
    ∀ k : ℕ, Finset (Fin (m * q)) → (Fin k → PreferenceOrder m) → ℝ
  | 0, _, _ => 0
  | k + 1, S, orders =>
      if hS : S.Nonempty then
        let chosen := favorite (liftPreference (orders 0)) S hS
        (rankOf (orders 0) (typeOf chosen) : ℝ) +
          serialTypeRankSum k (S.erase chosen) (Fin.tail orders)
      else 0

theorem serialTypeRankSum_bounds {m q : ℕ} (k : ℕ) (S : Finset (Fin (m * q)))
    (orders : Fin k → PreferenceOrder m) (hcard : S.card = k) :
    (k : ℝ) ≤ serialTypeRankSum k S orders ∧ serialTypeRankSum k S orders ≤ k * m := by
  induction k generalizing S with
  | zero => simp [serialTypeRankSum]
  | succ k ih =>
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      let chosen := favorite (liftPreference (orders 0)) S hS
      have hchosen : chosen ∈ S := favorite_mem _ _ _
      have herase : (S.erase chosen).card = k := by rw [Finset.card_erase_of_mem hchosen, hcard]; omega
      have htail := ih (S.erase chosen) (Fin.tail orders) herase
      have hr1 : (1 : ℝ) ≤ rankOf (orders 0) (typeOf chosen) := by
        exact_mod_cast (show 1 ≤ rankOf (orders 0) (typeOf chosen) by simp [rankOf])
      have hrm : (rankOf (orders 0) (typeOf chosen) : ℝ) ≤ m := by
        exact_mod_cast rankOf_le_marketSize (orders 0) (typeOf chosen)
      simp only [serialTypeRankSum, dif_pos hS, Nat.cast_add, Nat.cast_one]
      change (k : ℝ) + 1 ≤ (rankOf (orders 0) (typeOf chosen) : ℝ) +
          serialTypeRankSum k (S.erase chosen) (Fin.tail orders) ∧ _
      constructor <;> nlinarith [htail.1, htail.2]

def reindexProfile {m q : ℕ} (priority : Equiv.Perm (Fin (m * q))) :
    ReplicaPS.Profile m q ≃ ReplicaPS.Profile m q where
  toFun profile k := profile (priority k)
  invFun orders i := orders (priority.symm i)
  left_inv profile := by funext i; simp
  right_inv orders := by funext k; simp

def sample (m q : ℕ) :
    Finset (Equiv.Perm (Fin (m * q)) × ReplicaPS.Profile m q) :=
  permutationSample (Fin (m * q)) ×ˢ ReplicaPS.profileSample m q

lemma sample_nonempty (m q : ℕ) : (sample m q).Nonempty := by
  apply Finset.Nonempty.product
  · exact ⟨Equiv.refl _, Finset.mem_univ _⟩
  · exact ReplicaPS.profileSample_nonempty m q

/-- Realized average type rank for one priority order and preference profile. -/
def averageRank {m q : ℕ}
    (draw : Equiv.Perm (Fin (m * q)) × ReplicaPS.Profile m q) : ℝ :=
  serialTypeRankSum (m := m) (q := q) (m * q) Finset.univ
    (reindexProfile draw.1 draw.2) / (m * q : ℕ)

/-- The paper's RP rank at a fixed profile: priority randomness is averaged out. -/
def profileAverageRank {m q : ℕ} (profile : ReplicaPS.Profile m q) : ℝ :=
  𝔼 priority ∈ permutationSample (Fin (m * q)), averageRank (priority, profile)

def expectedRP (m q : ℕ) : ℝ := 𝔼 draw ∈ sample m q, averageRank draw

/-- Averaging joint draws gives the expectation of the paper's profile statistic. -/
theorem expectedRP_eq_expect_profileAverageRank (m q : ℕ) :
    expectedRP m q =
      𝔼 profile ∈ ReplicaPS.profileSample m q, profileAverageRank profile := by
  rw [expectedRP, sample, Finset.expect_product]
  exact Finset.expect_comm _ _ _

theorem averageRank_bounds {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (draw : Equiv.Perm (Fin (m * q)) × ReplicaPS.Profile m q) :
    1 ≤ averageRank draw ∧ averageRank draw ≤ m := by
  have hn : (0 : ℝ) < (m * q : ℕ) := by exact_mod_cast Nat.mul_pos hm hq
  have h := serialTypeRankSum_bounds (m := m) (q := q) (m * q) Finset.univ
    (reindexProfile draw.1 draw.2) (by simp)
  unfold averageRank
  constructor
  · apply (le_div_iff₀ hn).2
    simpa using h.1
  · apply (div_le_iff₀ hn).2
    simpa only [mul_comm] using h.2

theorem expectedRP_bounds {m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    1 ≤ expectedRP m q ∧ expectedRP m q ≤ m := by
  constructor
  · calc
      (1 : ℝ) = 𝔼 _draw ∈ sample m q, (1 : ℝ) := (Finset.expect_const (sample_nonempty m q) 1).symm
      _ ≤ expectedRP m q := Finset.expect_le_expect (fun draw _ => (averageRank_bounds hm hq draw).1)
  · calc
      expectedRP m q ≤ 𝔼 _draw ∈ sample m q, (m : ℝ) :=
        Finset.expect_le_expect (fun draw _ => (averageRank_bounds hm hq draw).2)
      _ = m := Finset.expect_const (sample_nonempty m q) _

theorem expectedRP_one_type {q : ℕ} (hq : 0 < q) : expectedRP 1 q = 1 := by
  have h := expectedRP_bounds (by omega : 0 < 1) hq
  norm_num at h
  exact le_antisymm h.2 h.1

end ProbabilisticSerial.ReplicaRP
