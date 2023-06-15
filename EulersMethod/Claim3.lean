import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
import Mathlib.Topology.MetricSpace.Basic

open scoped BoundedContinuousFunction

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E →ᵇ E)
variable (M:ℝ)
variable (x₀ : E)
variable (ε :ℝ)
variable (Ball_x₀_M : Metric.closedBall x₀ M)


lemma x_is_subset_of_Ball_at_initial  (t: Set.Icc 0 1)(x_bdd : ∀ ε, ∀ t ∈ Set.Icc 0 1, ‖x F x₀ ε t - x₀‖ ≤ M):  ∀t', (t' ∈ (x F x₀ ε) '' Set.Icc 0 1) → t' ∈ Metric.closedBall x₀ M  := by
intro t'
simp 
rw [dist_eq_norm]
intro x geqzero leqone func
rw [← func]
apply x_bdd
simp at t
exact ⟨ geqzero,leqone ⟩ 


lemma F_uniform_continuous (F' : Continuous F)(B : Metric.closedBall x₀ M ): UniformContinuous F:= by 
-- Heine_Cantor Theorem
sorry

#check x_subseq F x₀
#check F
#check y_c

theorem F_converges (F' : Continuous F) : ∀ (t : ((Set.Icc 0 1) : Set ℝ)),
  Filter.Tendsto (fun z => F (y_c F x₀ (x_subseq F x₀ z) t)) atTop (nhds (F (x_L F x₀ t))):= by  

sorry  
