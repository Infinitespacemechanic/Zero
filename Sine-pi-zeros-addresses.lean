import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

open Real Set Filter
open scoped Topology

noncomputable section

def factor (n : ℕ) (x : ℝ) : ℝ := 1 - x^2 / (n : ℝ)^2
def partialProd (N : ℕ) (x : ℝ) : ℝ :=
  (π * x) * ∏ n ∈ Finset.Icc 1 N, factor n x

/-! ### Converse: sin(πx)=0 → x is integer -/

-- Mathlib core: sin y = 0 ↔ y is an integer multiple of π
-- This is Real.sin_eq_zero_iff

theorem sin_pi_eq_zero_iff_int (x : ℝ) :
    sin (π * x) = 0 ↔ ∃ k : ℤ, x = k := by
  constructor
  · intro h
    -- sin(πx)=0 ↔ πx = n*π for some n:ℤ
    have hpi : π ≠ 0 := pi_ne_zero
    rw [sin_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    -- hk : π * x = k * π
    use k
    -- cancel π
    have : (k : ℝ) * π = π * x := by rw [hk, mul_comm]
    have : (k : ℝ) = x := by
      -- n*π = π*x → n = x  (π ≠ 0)
      field_simp at this ⊢
      linarith
    linarith
  · rintro ⟨k, rfl⟩
    exact sin_int_mul_pi k |>.trans (by rw [mul_comm])

-- Same as a set: zeros = ℤ
theorem sin_pi_zeros_eq_intCast : {x : ℝ | sin (π * x) = 0} = Set.range ((↑) : ℤ → ℝ) := by
  ext x
  simp [sin_pi_eq_zero_iff_int, Set.mem_range]

-- For the infinite product view: if sin(πx) ≠ 0, no factor vanishes
theorem factor_ne_zero_of_sin_ne_zero {x : ℝ} (hx : sin (π * x) ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    factor n x ≠ 0 := by
  unfold factor
  intro h
  have hx_int : ∃ k : ℤ, x = k := by
    by_contra h_not_int
    push_neg at h_not_int
    -- if factor n x = 0 then x = ±n, which would make sin = 0
    have : x^2 = (n : ℝ)^2 := by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp at h
      linarith
    have : x = (n : ℝ) ∨ x = -(n : ℝ) := by
      -- x² = n² → x = ±n
      have := sq_eq_sq_iff.mp this
      tauto
    rcases this with rfl | rfl
    · exact hx (sin_pi_eq_zero_iff_int _ |>.mpr ⟨n, rfl⟩)
    · exact hx (sin_pi_eq_zero_iff_int _ |>.mpr ⟨-n, by push_cast; ring⟩)
  obtain ⟨k, rfl⟩ := hx_int
  exact hx (sin_int_mul_pi k |>.trans (by rw [mul_comm]))

-- Locked limit still holds
theorem locked_euler_product (x : ℝ) :
    Tendsto (fun N => partialProd N x) atTop (𝓝 (sin (π * x))) :=
  Real.tendsto_euler_sin_prod x

end