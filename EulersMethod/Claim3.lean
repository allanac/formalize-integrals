import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
import Mathlib.Topology.MetricSpace.Basic

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)
variable (x₀ : E)
variable (ε :ℝ)
variable (x_bdd : ∀ t : Set.Icc 0 1, ‖x F x₀ ε t‖ ≤ M)
variable (Ball_x₀_M : Metric.closedBall x₀ M)

lemma x_is_subset_of_Ball_at_initial  (t: Set.Icc 0 1): (x F x₀ ε)'' Set.Icc 0 1 ⊂ Metric.closedBall x₀ M := by
--Claim 2
sorry  

lemma F_uniform_continuous (F' : Continuous F)(B : Metric.closedBall x₀ M ): UniformContinuous F:= by 
-- Heine_Cantor Theorem
sorry

Theorem F_converges:(F' : Continuous F),∀ t ∈ Icc 0 1,() F:= by  sorry  
