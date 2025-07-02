import CCchallengeLean.Collatz
import Mathlib.Data.Real.Basic
/-!
# Collatz cycles bounds

Collection of bounds on the size of elements in a Collatz cycle.
-/

/-- BohmSontacchi1978 (Proposition 6):

For every integer x such that $T^n(x) = x$, we have $|x| < 3^n$.

Note: the proof is simple.

Reference: [BohmSontacchi1978](https://ccchallenge.org/#BohmSontacchi1978)
-/
theorem BohmSontacchi1978_Prop_6
    (x : ℤ)
    (n : ℕ)
    (h : (T_Z^[n]) x = x) : |x| < 3^n :=
  sorry

theorem BohmSontacchi1978_Prop_6_Nat
    (x : ℕ)
    (n : ℕ)
    (h : (T^[n]) x = x) : x < 3^n :=
  sorry

/-- Rozier2022

For every natural number x such that $T^n(x) = x$, we have $x < 2^n$. A corollary is that we
also have $x < 3^k$ where $k$ is the number of odd indices in the first n iterations of T on x.

Note: the proof is (highly) nontrivial, relying on [Rhin1976](https://ccchallenge.org/#Rhin1976).
The corollary is easy to get using [Sterin2023](https://ccchallenge.org/#Sterin2023), see [sketch](https://forum.collatzworld.com/t/elementary-proof-of-x-2-n-in-a-cycle-of-size-n/67/4?u=cosmo).

Result also discussed in [this thread](https://forum.collatzworld.com/t/elementary-proof-of-x-2-n-in-a-cycle-of-size-n/67/4).

Reference: [Rozier2022](https://ccchallenge.org/#Rozier2022)
-/
theorem Rozier2022
    (x : ℕ)
    (n : ℕ)
    (h : (T^[n]) x = x) : x < 2^n :=
  sorry

theorem Rozier2022_corollary
    (x : ℕ)
    (n : ℕ)
    (k : ℕ)
    (h : (T^[n]) x = x)
    (h2 : (numOddIterates_T x n) = k) : x < 3^k :=
  sorry
