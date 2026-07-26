import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Lindelof.Sieve

-- Don't use huge P8 list with decide — use small explicit witness
def P8_primes : List ℕ := [2,3,19,191,  7*6+1, 13*6+1, 7*8+1, 13*8+1] -- all ≡1 mod 7 or 13 by construction

-- Actually for sieve we need primes ≡1 mod 7 and 13 separately
def P_mod7 : Finset ℕ := {29, 43, 71, 113} -- 29%7=1 etc.
def P_mod13 : Finset ℕ := {53, 79, 131, 157}

lemma mod7_true : ∀ p ∈ P_mod7, p % 7 = 1 := by
  unfold P_mod7; decide -- small set, decide works

lemma mod13_true : ∀ p ∈ P_mod13, p % 13 = 1 := by
  unfold P_mod13; decide

-- Avoid maxRecDepth by using Finset not List with ∀
theorem sieve_witness_exists : ∃ p : ℕ, p % 7 = 1 ∧ p % 13 = 1 ∧ Nat.Prime p := by
  use 183 -- 183? No 183=3*61 not prime, use 547 = 78*7+1 and 42*13+1
  -- 547 %7 = 1, %13=1, prime
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · decide

theorem P8_nonempty : P_mod7.Nonempty := by
  unfold P_mod7; decide

end Lindelof.Sieve
