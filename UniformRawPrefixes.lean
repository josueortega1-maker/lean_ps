import ReplicaRawProcess

/-! All raw-label prefix events can be placed on one finite iid sample. -/

noncomputable section
open Finset
open scoped BigOperators

namespace ProbabilisticSerial.UniformRawPrefixes
open UniformProduct CouponLowerBound ReplicaRawProcess

def dropNewest {m : ℕ} (k : ℕ) : (r : ℕ) → (Fin (k + r) → Fin m) → (Fin k → Fin m)
  | 0, w => w
  | r + 1, w => dropNewest k r (Fin.tail w)

lemma dropNewest_apply {m : ℕ} (k r : ℕ) (w : Fin (k + r) → Fin m) (i : Fin k) :
    dropNewest k r w i = w ⟨r + i.val, by omega⟩ := by
  induction r with
  | zero => simp [dropNewest]
  | succ r ih =>
      rw [dropNewest, ih]
      unfold Fin.tail
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

theorem expect_dropNewest {m : ℕ} (hm : 0 < m) (k r : ℕ)
    (F : (Fin k → Fin m) → ℝ) :
    (𝔼 w : Fin (k + r) → Fin m, F (dropNewest k r w)) = 𝔼 w : Fin k → Fin m, F w := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (𝔼 w : Fin ((k + r) + 1) → Fin m,
        F (dropNewest k r (Fin.tail w))) = _
      rw [ReplicaRawProcess.expect_fin_succ]
      simp only [dropNewest, Fin.tail_cons]
      rw [Finset.expect_const (show (Finset.univ : Finset (Fin m)).Nonempty from
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩)]
      exact ih

def rawPrefix {m N : ℕ} (k : ℕ) (hk : k ≤ N) (w : Fin N → Fin m) : Fin k → Fin m :=
  fun i => w ⟨N - k + i.val, by omega⟩

lemma prefix_eq_dropNewest {m : ℕ} (k r : ℕ) (w : Fin (k + r) → Fin m) :
    rawPrefix k (by omega) w = dropNewest k r w := by
  funext i
  rw [dropNewest_apply]
  unfold rawPrefix
  congr 1
  apply Fin.ext
  simp

theorem expect_prefix {m N k : ℕ} (hm : 0 < m) (hk : k ≤ N)
    (F : (Fin k → Fin m) → ℝ) :
    (𝔼 w : Fin N → Fin m, F (rawPrefix k hk w)) = 𝔼 w : Fin k → Fin m, F w := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp_rw [prefix_eq_dropNewest]
  exact expect_dropNewest hm k r F

lemma labelSample_eq_univ (m k : ℕ) : labelSample m k = Finset.univ := by
  simp [labelSample, productSample]

theorem probability_prefix {m N k : ℕ} (hm : 0 < m) (hk : k ≤ N)
    (event : (Fin k → Fin m) → Prop) [DecidablePred event] :
    probability (labelSample m N) (fun w => event (rawPrefix k hk w)) =
      probability (labelSample m k) event := by
  simp only [probability, labelSample_eq_univ]
  exact expect_prefix hm hk (fun w => if event w then (1 : ℝ) else 0)

def appendNew {m k : ℕ} (old : Fin k → Fin m) :
    (r : ℕ) → (Fin r → Fin m) → (Fin (k + r) → Fin m)
  | 0, _ => old
  | r + 1, new => Fin.cons (new 0) (appendNew old r (Fin.tail new))

theorem expect_appendNew {m : ℕ} (hm : 0 < m) (k r : ℕ)
    (F : (Fin (k + r) → Fin m) → ℝ) :
    (𝔼 w : Fin (k + r) → Fin m, F w) =
      𝔼 old : Fin k → Fin m, 𝔼 new : Fin r → Fin m, F (appendNew old r new) := by
  induction r with
  | zero =>
      simp only [appendNew, Finset.expect_const (show
        (Finset.univ : Finset (Fin 0 → Fin m)).Nonempty from ⟨Fin.elim0, Finset.mem_univ _⟩)]
      rfl
  | succ r ih =>
      change (𝔼 w : Fin ((k + r) + 1) → Fin m, F w) = _
      rw [ReplicaRawProcess.expect_fin_succ]
      simp_rw [ih]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro old hold
      rw [ReplicaRawProcess.expect_fin_succ]
      rfl

@[simp] lemma rawPrefix_self {m N : ℕ} (w : Fin N → Fin m) :
    rawPrefix N le_rfl w = w := by
  funext i
  simp [rawPrefix]

lemma rawPrefix_tail {m N k : ℕ} (hk : k ≤ N) (w : Fin (N + 1) → Fin m) :
    rawPrefix k hk (Fin.tail w) = rawPrefix k (by omega) w := by
  funext i
  unfold rawPrefix Fin.tail
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

end ProbabilisticSerial.UniformRawPrefixes
