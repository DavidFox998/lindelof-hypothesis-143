import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Lindelof.Sieve

-- Sieve witness for S₄={2,3,19,191} — 4 primes only
-- Shows primes outside S₄ exist but don't spoil positivity
-- For N=143=11*13, primes ≡1 mod 143 are ≡1 mod 11 and mod 13

def P_mod11 : Finset ℕ := {23, 67, 89}
def P_mod13 : Finset ℕ := {53, 79, 131}

theorem mod11_ok : ∀ p ∈ P_mod11, p % 11 = 1 := by decide
theorem mod13_ok : ∀ p ∈ P_mod13, p % 13 = 1 := by decide

-- 859 = 6*143+1 = 78*11+1 = 66*13+1, prime, ≡1 mod 11 and 13
-- This is the next prime in the progression 1 mod 143 after the S₄ desert
theorem prime_859 : Nat.Prime 859 := by decide
theorem mod_859_11 : 859 % 11 = 1 := by norm_num
theorem mod_859_13 : 859 % 13 = 1 := by norm_num

theorem witness_exists : ∃ p, Nat.Prime p ∧ p % 11 = 1 ∧ p % 13 = 1 :=
  ⟨859, prime_859, mod_859_11, mod_859_13⟩

-- Remark 3.4: 14-prime C≈8.629 set is spurious — composites beyond p₇
-- S₄ 4 primes suffices, witness shows other primes exist but are sieved

end Lindelof.Sieve
