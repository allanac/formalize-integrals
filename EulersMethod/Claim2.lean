import EulersMethod.Defs
import EulersMethod.Claim1

-- The xk(·) are uniformly bounded on [0,1]: 
-- sup sup |xk(t)| < ∞. k t∈[0,1]

open MeasureTheory
open Set
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)
theorem uniformlyBounded : ∃ M, ∀ ε > (0 : ℝ), ∀ t ∈ Icc 0 1, ‖x F x₀ ε t‖ ≤ M := by 
  use M + ‖x₀‖
  rintro ε ε_pos t ⟨tnn, tub⟩
  have : x F x₀ ε t = (x F x₀ ε t - x₀) + x₀ := by simp
  rw [this]
  calc
    ‖(x F x₀ ε t - x₀) + x₀‖ ≤ ‖x F x₀ ε t - x₀‖ + ‖x₀‖ := by
      apply norm_add_le
    _ ≤ M * t + ‖x₀‖ := by
      simp
      have : x F x₀ ε t - x₀ = x F x₀ ε t - x F x₀ ε 0 := by simp [ε_pos]
      rw [this]
      have : t = |t| := by
        symm
        rw [abs_eq]
        left; rfl
        exact tnn
      have : M * t = M * |t - 0| := by
        simp; left; exact this
      rw [this]
      apply Claim1
      all_goals
        first
        | linarith
        | done
      exact F_bdd
    _ ≤ _ := by
      simp
      calc
        M * t ≤ M * 1 := by
          apply mul_le_mul_of_nonneg_left <;> assumption
        _ ≤ _ := by simp
