import FiniteExposure
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite survivor averaging for the arrival bound

These lemmas prove the random-survivor Jensen and log-expectation steps.
They use explicit residual-capacity and exponential-process hypotheses.
ReplicaCapacity and ReplicaWeightedExposure identify these quantities on
the replica PS trace; no conditional independence of survivors is used.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteSurvivor

open FiniteExposure

lemma exp_average_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (v : ι → ℝ) :
    Real.exp ((∑ g ∈ S, v g) / S.card) ≤ (∑ g ∈ S, Real.exp (v g)) / S.card := by
  have hA : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have h := convexOn_exp.map_sum_le (t := S) (w := fun _ => (1 : ℝ) / S.card)
    (p := v) (fun _ _ => (one_div_pos.mpr hA).le)
    (by simp [hA.ne']) (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, one_div_mul_eq_div, ← Finset.sum_div] using h

def normalizedTotal {m : ℕ} (M : Fin m → ℝ) : ℝ := (∑ g, M g) / m

lemma normalizedTotal_pos {m : ℕ} (hm : 0 < m) (M : Fin m → ℝ)
    (hM : ∀ g, 0 < M g) : 0 < normalizedTotal M := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact div_pos (Finset.sum_pos (fun g _ => hM g) hne) hmR

theorem survivor_log_envelope {m : ℕ} (hm : 0 < m) {q θ u F : ℝ}
    (hq : 0 < q) (hθ : 0 < θ) (hu : 0 < u)
    (S : Finset (Fin m)) (r M : Fin m → ℝ)
    (hrq : ∀ g ∈ S, r g ≤ q)
    (hresidual : (∑ g ∈ S, r g) = m * q * u)
    (hM : ∀ g, 0 < M g)
    (hentry : ∀ g ∈ S, Real.exp (F - θ * (q - r g)) ≤ M g) :
    F ≤ phi (q * θ) u + Real.log (normalizedTotal M) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hresidual
    nlinarith [mul_pos (mul_pos hmR hq) hu]
  have hA : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hAm : (S.card : ℝ) ≤ m := by
    exact_mod_cast (show S.card ≤ m by simpa using Finset.card_le_univ S)
  let a : ℝ := S.card / m
  have ha : 0 < a := div_pos hA hmR
  have ha1 : a ≤ 1 := (div_le_one hmR).2 hAm
  have hcap : m * q * u ≤ (S.card : ℝ) * q := by
    rw [← hresidual]
    calc
      (∑ g ∈ S, r g) ≤ ∑ _g ∈ S, q := Finset.sum_le_sum hrq
      _ = _ := by simp
  have hua : u ≤ a := by
    apply (le_div_iff₀ hmR).2
    nlinarith
  have hmean : (∑ g ∈ S, (F - θ * (q - r g))) / S.card =
      F - q * θ * (1 - u / a) := by
    have hid (g : Fin m) : F - θ * (q - r g) = (F - θ * q) + θ * r g := by ring
    simp_rw [hid, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hresidual]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [a]
    field_simp [hA.ne', hmR.ne']
    <;> ring
  have hj := exp_average_le S hS (fun g => F - θ * (q - r g))
  rw [hmean] at hj
  have hs : (S.card : ℝ) * Real.exp (F - q * θ * (1 - u / a)) ≤ ∑ g, M g := by
    calc
      _ ≤ ∑ g ∈ S, Real.exp (F - θ * (q - r g)) := by
        have h := (le_div_iff₀ hA).mp hj
        simpa only [mul_comm] using h
      _ ≤ ∑ g ∈ S, M g := Finset.sum_le_sum hentry
      _ ≤ ∑ g, M g := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ S) (fun g _ _ => (hM g).le)
  have hnorm : a * Real.exp (F - q * θ * (1 - u / a)) ≤ normalizedTotal M := by
    have h := div_le_div_of_nonneg_right hs hmR.le
    simpa only [a, normalizedTotal, div_mul_eq_mul_div] using h
  have hl := Real.log_le_log (mul_pos ha (Real.exp_pos _)) hnorm
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have hobj := objective_le_phi (mul_pos hq hθ) hu hua ha1
  dsimp [objective] at hobj
  linarith

theorem endpoint_log_envelope {m : ℕ} (hm : 0 < m) {q θ F : ℝ}
    (M : Fin m → ℝ) (hM : ∀ g, 0 < M g)
    (hlast : ∃ g, Real.exp (F - q * θ) ≤ M g) :
    F ≤ q * θ + Real.log (m : ℝ) + Real.log (normalizedTotal M) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨g, hg⟩ := hlast
  have hs : Real.exp (F - q * θ) ≤ ∑ j, M j :=
    hg.trans (Finset.single_le_sum (fun j _ => (hM j).le) (Finset.mem_univ g))
  have htotal : (∑ j, M j) = (m : ℝ) * normalizedTotal M := by
    unfold normalizedTotal
    field_simp [hmR.ne']
  have hl := Real.log_le_log (Real.exp_pos _) hs
  rw [Real.log_exp, htotal, Real.log_mul hmR.ne' (normalizedTotal_pos hm M hM).ne'] at hl
  linarith

lemma expected_normalizedTotal_le_one {Ω : Type*} {m : ℕ} (hm : 0 < m)
    (s : Finset Ω) (M : Ω → Fin m → ℝ)
    (hmean : ∀ g, (𝔼 ω ∈ s, M ω g) ≤ 1) :
    (𝔼 ω ∈ s, normalizedTotal (M ω)) ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [normalizedTotal, ← Finset.expect_div, Finset.expect_sum_comm]
  apply (div_le_one hmR).2
  calc
    (∑ g, 𝔼 ω ∈ s, M ω g) ≤ ∑ _g : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum (fun g _ => hmean g)
    _ = m := by simp

theorem expected_compensator_le {Ω : Type*} {m : ℕ} (hm : 0 < m)
    (s : Finset Ω) (hs : s.Nonempty) {q θ u : ℝ}
    (hq : 0 < q) (hθ : 0 < θ) (hu : 0 < u)
    (S : Ω → Finset (Fin m)) (r M : Ω → Fin m → ℝ) (F : Ω → ℝ)
    (hrq : ∀ ω ∈ s, ∀ g ∈ S ω, r ω g ≤ q)
    (hresidual : ∀ ω ∈ s, (∑ g ∈ S ω, r ω g) = m * q * u)
    (hM : ∀ ω ∈ s, ∀ g, 0 < M ω g)
    (hentry : ∀ ω ∈ s, ∀ g ∈ S ω, Real.exp (F ω - θ * (q - r ω g)) ≤ M ω g)
    (hmean : ∀ g, (𝔼 ω ∈ s, M ω g) ≤ 1) :
    (𝔼 ω ∈ s, F ω) ≤ phi (q * θ) u := by
  apply expect_le_of_log_envelope s hs F (fun ω => normalizedTotal (M ω)) _
    (fun ω hω => normalizedTotal_pos hm (M ω) (hM ω hω))
    (expected_normalizedTotal_le_one hm s M hmean)
  intro ω hω
  exact survivor_log_envelope hm hq hθ hu (S ω) (r ω) (M ω)
    (hrq ω hω) (hresidual ω hω) (hM ω hω) (hentry ω hω)

theorem expected_endpoint_compensator_le {Ω : Type*} {m : ℕ} (hm : 0 < m)
    (s : Finset Ω) (hs : s.Nonempty) (q θ : ℝ)
    (M : Ω → Fin m → ℝ) (F : Ω → ℝ)
    (hM : ∀ ω ∈ s, ∀ g, 0 < M ω g)
    (hlast : ∀ ω ∈ s, ∃ g, Real.exp (F ω - q * θ) ≤ M ω g)
    (hmean : ∀ g, (𝔼 ω ∈ s, M ω g) ≤ 1) :
    (𝔼 ω ∈ s, F ω) ≤ q * θ + Real.log (m : ℝ) := by
  apply expect_le_of_log_envelope s hs F (fun ω => normalizedTotal (M ω)) _
    (fun ω hω => normalizedTotal_pos hm (M ω) (hM ω hω))
    (expected_normalizedTotal_le_one hm s M hmean)
  intro ω hω
  exact endpoint_log_envelope hm (M ω) (hM ω hω) (hlast ω hω)

end ProbabilisticSerial.FiniteSurvivor
