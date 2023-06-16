import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Compact

open scoped BoundedContinuousFunction
open Filter

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


--lemma F_uniform_continuous (F' : Continuous F): UniformContinuous F:= by 
--apply CompactSpace.uniformContinuous_of_continuous F'
-- Heine_Cantor Theorem
--sorry

#check x_subseq F x₀
#check F
#check y_c
#check (fun z =>(fun t : ℝ => F (y_c F x₀ (x_subseq F x₀ z) (Set.projIcc 0 1 (by norm_num) t))))
#check y_converges
#check ((x_L F x₀).toFun)

theorem F_converges (F' : Continuous F) : ∀ t : ℝ,
  Tendsto (fun z =>(F (y_c F x₀ (x_subseq F x₀ z) (Set.projIcc 0 1 (by norm_num) t)))) 
    atTop (nhds (F (x_L F x₀ (Set.projIcc 0 1 (by norm_num) t)))) := by  
      
      intro t
      have y_conv := (y_converges F x₀).tendsto_at (Set.projIcc 0 1 (by norm_num) t)
      have F_conv := (Continuous.tendsto F' ((x_L F x₀).toFun (Set.projIcc 0 1 (by norm_num) t)))
      apply Tendsto.comp F_conv y_conv
