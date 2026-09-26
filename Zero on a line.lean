/-
  Zero on a line.lean
  Zero is a location, a meeting point, a destination.
  This location has zero chickens.

  Formal idea: zero is not "nothing", it's an address on the line.
  sin(πx) must travel through it because a factor forces it to.

  Primes are just some of those addresses. Same line, same algebra.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

noncomputable section

-- Zero as a location
def ZeroLocation : ℝ := 0

def Address (n : ℤ) : ℝ := n

-- A factor forces a meeting at its address
structure ForcedMeeting where
  n : ℕ
  planted : ℝ
  forces : planted = n ∨ planted = -n

def factorForces (n : ℕ) (hn : n ≠ 0) : ForcedMeeting :=
  ⟨n, n, Or.inl rfl⟩

-- Meeting point: all factors agree to meet at 0 at some point?
-- sin(πx) is the function that travels between meetings

theorem all_addresses_meet_at_zero (k : ℤ) : sin (π * k) = 0 :=
  sin_int_mul_pi k |>.trans (by rw [mul_comm])

-- Chickens remain zero at every stop, prime or not
def chickensAt (x : ℝ) : ℕ := 0

theorem chickens_zero_at_every_address (x : ℝ) : chickensAt x = 0 := rfl

theorem chickens_zero_at_prime_addresses (p : ℕ) : chickensAt p = 0 := rfl

-- The line itself is just ℝ, zeros are ℤ sitting inside it
theorem addresses_embed_in_line : (Set.range ((↑) : ℤ → ℝ)) ⊆ (Set.univ : Set ℝ) :=
  Set.subset_univ _

-- Zero is not special as "nothing", it's special as origin address
-- planted by πx
theorem origin_planted_by_pi_factor : ZeroLocation = 0 := rfl

theorem pi_factor_vanishes_at_origin : Real.pi * ZeroLocation = 0 := by
  simp [ZeroLocation]

end
