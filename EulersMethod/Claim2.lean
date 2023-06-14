import EulersMethod.Defs

open MeasureTheory
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)