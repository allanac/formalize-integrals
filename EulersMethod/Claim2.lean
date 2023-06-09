import EulersMethod.Defs
import EulersMethod.Claim1

-- The xk(·) are uniformly bounded on [0,1]: 
-- sup sup |xk(t)| < ∞. k t∈[0,1]

open scoped BoundedContinuousFunction

open MeasureTheory
open Set
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E →ᵇ E)
variable (x₀ : E)

-- variable (M : ℝ) (M_nn : 0 ≤ M)
-- variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)
theorem uniformlyBounded : ∃ M, ∀ ε > (0 : ℝ), ∀ t ∈ Icc 0 1, ‖x F x₀ ε t‖ ≤ M := by 
  use M F + ‖x₀‖
  rintro ε ε_pos t ⟨tnn, tub⟩
  have : x F x₀ ε t = (x F x₀ ε t - x₀) + x₀ := by simp
  rw [this]
  calc
    ‖(x F x₀ ε t - x₀) + x₀‖ ≤ ‖x F x₀ ε t - x₀‖ + ‖x₀‖ := by
      apply norm_add_le
    _ ≤ M F * t + ‖x₀‖ := by
      simp
      have : x F x₀ ε t - x₀ = x F x₀ ε t - x F x₀ ε 0 := by simp [ε_pos]
      rw [this]
      have : t = |t| := by
        symm
        rw [abs_eq]
        left; rfl
        exact tnn
      have : M F * t = M F * |t - 0| := by
        simp; left; exact this
      rw [this]
      apply Claim1
      all_goals
        first
        | linarith
      -- exact F_bdd
    _ ≤ _ := by
      simp
      calc
        M F * t ≤ M F * 1 := by
          apply mul_le_mul_of_nonneg_left
          exact tub
          apply norm_nonneg
        _ ≤ _ := by simp
