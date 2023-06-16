import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
import EulersMethod.IntegralEq
--import Std.Tactic.Infer

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem peano_existance_F_bdd (G : E →ᵇ E) (x₀ : E) :
  (∃ x : ℝ → E,  (∃ x' : ℝ → E,
    Continuous x' ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (x' t) t ∧ x' t = G (x t) ∧ x 0 = x₀)) := by
      let x_L_ex := Function.extend Subtype.val (x_L G x₀).toFun 0
      use x_L_ex
      let x_L_ex' := (fun z => G (x_L_ex z))
      use x_L_ex'
      constructor
      · sorry
      · intro t ht
        have ftc := xL_eq_integ G x₀ 
        have hasderiv : ∀ z, HasDerivAt x_L_ex (x_L_ex' t) z := by sorry
        have ftc_t : x_L' G x₀ t = x₀ + ∫ (s : ℝ) in (0)..(t), G (x_L' G x₀ s) := ftc t ht
        have ftc_0 := ftc 0 (by norm_num)
        constructor
        · apply hasderiv
        · constructor
          · rw [← HasDerivAt.deriv (hasderiv t)]
            have : deriv x_L_ex t = deriv (fun z => (x_L_ex z - x₀)) t := by sorry
            rw [this]
            sorry
          · rw [intervalIntegral.integral_same] at ftc_0
            rw [add_zero] at ftc_0
            sorry
        
