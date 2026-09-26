/-
  Sine-pi-zeros-addresses.lean
  Zero is a location. sin(πx) vanishes exactly at those locations.

  Picture: πx plants 0, each (1 - x²/n²) plants ±n.
  No extra geometry, just addresses. Primes are just some addresses.
  Chickens remain zero at every stop.

  This file is sorry-free via Mathlib's Euler product.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

open Real Finset Filter
open scoped Topology

noncomputable section

def factor (n : ℕ) (x : ℝ) : ℝ := 1 - x^2 / (n : ℝ)^2

def partialProd (N : ℕ) (x : ℝ) : ℝ :=
  (π * x) * ∏ n ∈ Icc 1 N, factor n x

-- πx plants the origin
theorem zero_planted_by_pi_x (N : ℕ) : partialProd N 0 = 0 := by
  simp [partialProd, factor]

-- 1 - n²/n² = 0 plants n
theorem factor_plants_n (n : ℕ) (hn : n ≠ 0) : factor n n = 0 := by
  unfold factor
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp; ring

theorem factor_plants_neg_n (n : ℕ) (hn : n ≠ 0) : factor n (-(n : ℝ)) = 0 := by
  unfold factor
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp; ring

-- The finite product is zero on its covered addresses
theorem partialProd_zero_on_address {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    partialProd N k = 0 ∧ partialProd N (-(k : ℝ)) = 0 := by
  constructor
  · unfold partialProd
    have hmem : k ∈ Icc 1 N := mem_Icc.mpr ⟨hk, hkN⟩
    have h0 : factor k (k : ℝ) = 0 := factor_plants_n k (by omega)
    calc (π * (k : ℝ)) * ∏ n ∈ Icc 1 N, factor n (k : ℝ)
        = _ * 0 := by congr; exact prod_eq_zero hmem h0
      _ = 0 := mul_zero _
  · unfold partialProd
    have hmem : k ∈ Icc 1 N := mem_Icc.mpr ⟨hk, hkN⟩
    have h0 : factor k (-(k : ℝ)) = 0 := factor_plants_neg_n k (by omega)
    calc (π * -(k : ℝ)) * ∏ n ∈ Icc 1 N, factor n (-(k : ℝ))
        = _ * 0 := by congr; exact prod_eq_zero hmem h0
      _ = 0 := mul_zero _

-- Every integer address is a zero of sin(πx)
theorem sin_pi_zero_at_int (k : ℤ) : sin (π * k) = 0 :=
  sin_int_mul_pi k |>.trans (by rw [mul_comm])

-- Converse: if sin(πx)=0 then x is an integer address
theorem sin_pi_zero_iff_int (x : ℝ) : sin (π * x) = 0 ↔ ∃ k : ℤ, x = k := by
  constructor
  · intro h
    rw [sin_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    use k
    have h1 : (k : ℝ) * π = π * x := by rw [← hk]; ring
    have hpi : π ≠ 0 := pi_ne_zero
    field_simp at h1 ⊢
    linarith
  · rintro ⟨k, rfl⟩
    exact sin_pi_zero_at_int k

-- The red dots are exhaustive: {x | sin(πx)=0} = ℤ
theorem zeros_are_exactly_integers :
    {x : ℝ | sin (π * x) = 0} = Set.range ((↑) : ℤ → ℝ) := by
  ext x; simp [sin_pi_zero_iff_int, Set.mem_range]

-- Euler product, locked: P_N → sin(πx)
-- The wild swings for small N get tamed
theorem euler_product_locked (x : ℝ) :
    Tendsto (fun N => partialProd N x) atTop (𝓝 (sin (π * x))) :=
  Real.tendsto_euler_sin_prod x

-- Complex version for completeness
theorem euler_product_complex (z : ℂ) :
    Filter.Tendsto (fun N => (↑Real.pi * z) * ∏ n ∈ Icc 1 N, (1 - z^2 / (n : ℂ)^2))
      atTop (𝓝 (Complex.sin (↑Real.pi * z))) :=
  Complex.tendsto_euler_sin_prod z

end
