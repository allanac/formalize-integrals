import EulersMethod.Defs
import EulersMethod.Claim1

-- The xk(·) are uniformly bounded on [0,1]: 
-- sup sup |xk(t)| < ∞. k t∈[0,1]


#check Claim1

open MeasureTheory
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)

theorem uniformlyBounded {EE: Type ℝ_} x x₀ : ℝ := by sorry