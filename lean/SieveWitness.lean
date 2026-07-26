import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Lindelof.Sieve
def P_mod7 : Finset ℕ := {29, 43, 71}
def P_mod13 : Finset ℕ := {53, 79, 131}

theorem mod7_ok : ∀ p ∈ P_mod7, p % 7 = 1 := by decide
theorem mod13_ok : ∀ p ∈ P_mod13, p % 13 = 1 := by decide

-- 547 = 78*7+1 = 42*13+1, prime
theorem prime_547 : Nat.Prime 547 := by decide
theorem mod_547_7 : 547 % 7 = 1 := by norm_num
theorem mod_547_13 : 547 % 13 = 1 := by norm_num

theorem witness_exists : ∃ p, Nat.Prime p ∧ p % 7 = 1 ∧ p % 13 = 1 :=
  ⟨547, prime_547, mod_547_7, mod_547_13⟩
end Lindelof.Sieve
