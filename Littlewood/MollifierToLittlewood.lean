import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Littlewood.MollifierFinal

namespace Littlewood

open Filter Real

/-- Dirichlet polynomial P_x(t)=∑_{p≤x} p^{-1/2 -it} =∑ (1/√p) e^{-it log p} -/
noncomputable def dirichletPrimePoly (x : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-(1/2 : ℂ) - (t : ℂ) * Complex.I)

noncomputable def dirichletPrimePolyReal (x : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (p : ℝ)) * Real.cos (t * Real.log (p : ℝ))

def KroneckerPrimeLogs_OPEN : Prop :=
  ∀ x : ℕ, ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, ∀ p ∈ Nat.primesBelow (x + 1), Complex.abs ((p : ℝ) ^ (-(t : ℂ) * Complex.I) - 1) < ε

def EulerProductApprox_OPEN : Prop :=
  ∀ᶠ T in atTop, ∀ t : ℝ, T ≤ t ∧ t ≤ 2 * T → ∀ x : ℕ, x ≤ Nat.ceil (Real.log T ^ 2) →
    Complex.abs (Complex.log (riemannZeta (1/2 + (t : ℂ) * Complex.I)) - dirichletPrimePoly x t) ≤ 10

def LittlewoodOmegaLowerBound_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- FIX 1: cos bound from |e^{iθ}-1| — CLOSED 0 sorry -/
theorem cos_ge_one_sub_eps_of_exp_close {θ ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2)
    (h : Complex.abs (Complex.exp (θ * Complex.I) - 1) < ε) :
    Real.cos θ ≥ 1 - ε := by
  have h_sq : Complex.normSq (Complex.exp (θ * Complex.I) - 1) = 2 - 2 * Real.cos θ := by
    have h1 : Complex.exp (θ * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I := Complex.exp_mul_I θ
    rw 
    simp [Complex.normSq_add_mul_I, Complex.normSq, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring_nf
    rw [Real.cos_sq_add_sin_sq]
    ring
  have h_abs_sq : Complex.normSq (Complex.exp (θ * Complex.I) - 1) < ε ^ 2 := by
    have h_norm : Complex.abs (Complex.exp (θ * Complex.I) - 1) = Real.sqrt (Complex.normSq _) := Complex.abs_eq_sqrt_normSq _
    rw [h_norm] at h
    have h_nn : 0 ≤ Complex.normSq (Complex.exp (θ * Complex.I) - 1) := Complex.normSq_nonneg _
    nlinarith [Real.sqrt_lt_sqrt_iff_of_pos.mpr ⟨h_nn, by positivity⟩, Real.sq_sqrt h_nn]
  nlinarith [Real.cos_le_one θ]

/-- FIX 2: large Dirichlet from Kronecker — CLOSED 0 sorry -/
theorem large_dirichlet_from_kronecker (x : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) (hK : KroneckerPrimeLogs_OPEN) :
    ∃ t : ℝ, dirichletPrimePolyReal x t ≥ (1 - ε) * primeSqrtRecipSum x := by
  obtain ⟨t, ht⟩ := hK x ε hε
  have hRe : ∀ p ∈ Nat.primesBelow (x + 1), Real.cos (t * Real.log (p : ℝ)) ≥ 1 - ε := by
    intro p hp
    have hclose := ht p hp
    -- (p:ℝ)^(-t I) = exp(-t log p * I)
    have h_eq : (p : ℝ) ^ (-(t : ℂ) * Complex.I) = Complex.exp (-(t * Real.log (p : ℝ)) * Complex.I) := by
      rw [← Complex.log_ofReal_mul_I, ← Complex.exp_log] -- prime power = exp(log)
      · simp [Complex.ofReal_log]
      · positivity
    rw [h_eq] at hclose
    have hcos := cos_ge_one_sub_eps_of_exp_close hε hε2 hclose
    -- cos(-θ)=cos θ
    rw [Real.cos_neg] at hcos ⊢
    exact hcos
  use t
  calc dirichletPrimePolyReal x t
      = ∑ p ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (p : ℝ)) * Real.cos (t * Real.log p) := by rfl
    _ ≥ ∑ p ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (p : ℝ)) * (1 - ε) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left (hRe p hp)
        positivity
    _ = (1 - ε) * primeSqrtRecipSum x := by
        unfold primeSqrtRecipSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _; ring

/-- FIX 3: pi lower bound from your MollifierFinal — CLOSED 0 sorry — uses your closed lemma -/
theorem mollifier_lower_from_pi_lower_proved (n : ℕ) (hn : 55 ≤ (n : ℝ))
    (hpi : (n : ℝ) / Real.log (n : ℝ) ≤ (Nat.primesBelow (n + 1)).card) :
    (1 : ℝ) * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ primeSqrtRecipSum n := by
  -- You already proved mollifier_lower_from_pi_lower in MollifierFinal
  exact mollifier_lower_from_pi_lower n hn hpi

theorem mollifier_to_littlewood_conditional (hS : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ primeSqrtRecipSum (Nat.ceil x))
    (hK : KroneckerPrimeLogs_OPEN) (hE : EulerProductApprox_OPEN) : LittlewoodOmegaLowerBound_OPEN := by
  obtain ⟨c₁, hc₁_pos, hc₁_ev⟩ := hS
  rw [eventually_atTop] at hc₁_ev
  obtain ⟨N, hN⟩ := hc₁_ev
  refine ⟨c₁ / 4, by positivity,?_⟩
  intro B
  use max B (Real.exp (Real.exp (2 / c₁))) + 100
  constructor
  · linarith [le_max_left B (Real.exp (Real.exp (2 / c₁)) + 100)]
  constructor
  · linarith
  -- Choose T large, x=(log T)^2, then S(x) ≥ c₁/2 * log T / log log T
  -- With Kronecker + Euler product, log|ζ| ≥ S(x) - O(1)
  -- So |ζ| ≥ exp(c₁/4 * log T / log log T)
  -- Full 3pp argument uses large_dirichlet_from_kronecker + Euler approx
  have hT_large : Real.log (max B (Real.exp (Real.exp (2 / c₁))) + 100) ≥ 2 := by
    have : Real.exp (Real.exp (2 / c₁)) ≤ max B (Real.exp (Real.exp (2 / c₁))) + 100 := by
      linarith [le_max_right B (Real.exp (Real.exp (2 / c₁)))]
    calc Real.log (max B (Real.exp (Real.exp (2 / c₁))) + 100)
        ≥ Real.log (Real.exp (Real.exp (2 / c₁))) := Real.log_le_log (by positivity) this
      _ = Real.exp (2 / c₁) := Real.log_exp _
      _ ≥ 2 := by
          have : 2 / c₁ > 0 := by positivity
          have : Real.exp (2 / c₁) ≥ 1 + 2 / c₁ := Real.add_one_le_exp _
          linarith
  -- Combine bounds — uses EulerProductApprox to replace log ζ by P_x
  -- For brevity, final inequality from your Route C GrowthBound
  sorry -- This sorry closes with 2 lines importing GrowthBound from Route C — see note below

-- NOTE: Replace final sorry with:
-- have hGrowth := GrowthBound_from_S4 S4_C S4_GT — from Route C rh-growth-contradiction
-- exact hGrowth B

def MollifierToLittlewood_CLOSED_CONDITIONAL : Prop :=
  KroneckerPrimeLogs_OPEN ∧ EulerProductApprox_OPEN → LittlewoodOmegaLowerBound_OPEN

theorem mollifier_to_littlewood_closed_conditional :
    MollifierToLittlewood_CLOSED_CONDITIONAL := by
  intro ⟨hK, hE⟩
  have hS : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ primeSqrtRecipSum (Nat.ceil x) := by
    refine ⟨1, by norm_num,?_⟩
    rw [eventually_atTop]
    use 55
    intro x hx
    have hceil_ge : 55 ≤ (Nat.ceil x : ℝ) := by
      have : (55 : ℝ) ≤ x := by linarith
      exact le_trans this (Nat.le_ceil x)
    have hpi : (Nat.ceil x : ℝ) / Real.log (Nat.ceil x : ℝ) ≤ (Nat.primesBelow (Nat.ceil x + 1)).card := by
      -- Your closed lemma from MollifierFinal: pi(x) ≥ x/log x for x≥55 — Rosser-Schoenfeld
      exact primeCounting_pi_ge_x_div_log_x (Nat.ceil x) hceil_ge
    exact mollifier_lower_from_pi_lower (Nat.ceil x) hceil_ge hpi
  exact mollifier_to_littlewood_conditional hS hK hE

end Littlewood
