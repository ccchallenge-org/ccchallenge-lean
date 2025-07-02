import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Collatz functions

Define Collatz functions.
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
  Finset.range (n + 1) |>.filter (λ i : ℕ => Odd (C^[i] x))

def oddIterateIndices_C_Z (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (λ i : ℕ => Odd (C_Z^[i] x))

def oddIterateIndices_T (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (λ i : ℕ => Odd (T^[i] x))

def oddIterateIndices_T_Z (x n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) |>.filter (λ i : ℕ => Odd (T_Z^[i] x))
