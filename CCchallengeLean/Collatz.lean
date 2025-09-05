import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Collatz functions

Define Collatz functions.

TODO:
  - add definition of the Collatz functions over ℤ_2, see
  https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Defining.20the.20Collatz.20function.20of.20the.202-adic.20integers/with/526802315
-/

def C (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

def C_Z (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

def T (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1)/2

def T_Z (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1)/2

def oddIterateIndices_C (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (fun i : ℕ => Odd (C^[i] x))

def numOddIterates_C (x n : ℕ) : ℕ :=
  (oddIterateIndices_C x n).card

def oddIterateIndices_C_Z (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (fun i : ℕ => Odd (C_Z^[i] x))

def numOddIterates_C_Z (x n : ℕ) : ℕ :=
  (oddIterateIndices_C_Z x n).card

def oddIterateIndices_T (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (fun i : ℕ => Odd (T^[i] x))

def numOddIterates_T (x n : ℕ) : ℕ :=
  (oddIterateIndices_T x n).card

def oddIterateIndices_T_Z (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (fun i : ℕ => Odd (T_Z^[i] x))

def numOddIterates_T_Z (x n : ℕ) : ℕ :=
  (oddIterateIndices_T_Z x n).card
