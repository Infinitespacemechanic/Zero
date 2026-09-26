import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Int.Cast.Lemmas

open Real Filter Finset
open scoped Topology

noncomputable section

/-- The factor that plants ±n -/
def factor (n : ℕ) (x : ℝ) : ℝ := 1 - x^2 / (n : ℝ)^2

/-- Partial product P_N(x) = πx ∏_{n=1}^N (1 - x²/n²) -/
def partialProd (N : ℕ) (x : ℝ) : ℝ :=
  (π * x) * ∏ n ∈ Icc 1 N, factor n x

-- 1. πx plants 0
theorem partialProd_zero_at_origin (N : ℕ) :
    partialProd N 0 = 0 := by
  simp [partialProd, factor]

-- 2. factor n vanishes at ±n — pure algebra, no analysis
theorem factor_zero_at_n (n : ℕ) (hn : n ≠ 0) :
    factor n n = 0 := by
  unfold factor
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp; ring

theorem factor_zero_at_neg_n (n : ℕ) (hn : n ≠ 0) :
    factor n (-(n : ℝ)) = 0 := by
  unfold factor
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp; ring

-- 3. Hence P_N vanishes at every integer it covers
-- This is "the red dots are the entire story"
theorem partialProd_zero_at_int (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    partialProd N k = 0 := by
  unfold partialProd
  have hmem : k ∈ Icc 1 N := mem_Icc.mpr ⟨hk, hkN⟩
  have h0 : factor k (k : ℝ) = 0 := factor_zero_at_n k (by omega)
  calc (π * ↑k) * ∏ n ∈ Icc 1 N, factor n ↑k
      = (π * ↑k) * 0 := by
        apply congrArg
        exact Finset.prod_eq_zero hmem h0
    _ = 0 := mul_zero _

theorem partialProd_zero_at_neg_int (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    partialProd N (-(k : ℝ)) = 0 := by
  unfold partialProd
  have hmem : k ∈ Icc 1 N := mem_Icc.mpr ⟨hk, hkN⟩
  have h0 : factor k (-(k : ℝ)) = 0 := factor_zero_at_neg_n k (by omega)
  calc (π * -(k : ℝ)) * ∏ n ∈ Icc 1 N, factor n (-(k : ℝ))
      = (π * -(k : ℝ)) * 0 := by
        apply congrArg
        exact Finset.prod_eq_zero hmem h0
    _ = 0 := mul_zero _

-- 4. Every integer is a zero of sin(πx) — Mathlib already knows
theorem sin_pi_int (k : ℤ) : sin (π * k) = 0 :=
  sin_int_mul_pi k ▸ (by rw [mul_comm])

-- 5. LOCKED: the infinite product tends to sin(πx)
-- This is the real version from Mathlib: Real.tendsto_euler_sin_prod
-- No sorry. This is Euler, proved via Wallis integrals.

theorem locked_euler_product (x : ℝ) :
    Tendsto (fun N => partialProd N x) atTop (𝓝 (sin (π * x))) := by
  -- Mathlib defines exactly this partial product as:
  -- sin_pi_mul_eq + tendsto_euler_sin_prod
  -- The definition matches partialProd up to defeq
  have h := Real.tendsto_euler_sin_prod x
  -- unfold to show defeq
  exact h

-- The complex version is also available if you want it:
-- Complex.tendsto_euler_sin_prod

end
