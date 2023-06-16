import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
import EulersMethod.IntegralEq
--import Std.Tactic.Infer

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem peano_existance_F_bdd' (G : E →ᵇ E) :
  (∃ x : ℝ → E,  (∃ x' : ℝ → E,
    Continuous x' ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (x' t) t ∧ x' t = G (x t) ∧ x 0 = 0)) := by
      let x_L_ex := x_L' G 0
      use x_L_ex
      let x_L_ex' := (fun z => G (x_L_ex z))
      use x_L_ex'
      let x_L_ex_2 := (fun z => ∫ (s : ℝ) in (0)..(z), G (x_L' G 0 s))
      constructor
      · sorry
      · intro t ht
        have ftc := xL_eq_integ G 0
        have ftc' : ∀ (z : ℝ), z ∈ Set.Icc 0 1 → x_L' G 0 z = ∫ (s : ℝ) in (0)..(z), G (x_L' G 0 s) := by
          intro z hz
          rw [ftc z hz]
          apply zero_add
        have hasderiv : ∀ z, HasDerivAt x_L_ex (x_L_ex' z) z := by
          intro z
          have : HasDerivAt x_L_ex_2 (x_L_ex' z) z := by
            apply intervalIntegral.integral_hasDerivAt_right
            sorry
            --apply Fy_measurable G 0 0 z
          sorry
        have ftc_t : x_L' G 0 t = 0 + ∫ (s : ℝ) in (0)..(t), G (x_L' G 0 s) := ftc t ht
        rw [zero_add] at ftc_t
        have ftc_0 := ftc 0 (by norm_num)
        rw [zero_add] at ftc_0
        constructor
        · apply hasderiv
        · constructor
          · rw [← HasDerivAt.deriv (hasderiv t)]
            sorry
          · rw [intervalIntegral.integral_same] at ftc_0
            exact ftc_0

theorem peano_existance_F_bdd (G : E →ᵇ E) (x₀ : E):
  (∃ x : ℝ → E,  (∃ x' : ℝ → E,
    Continuous x' ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (x' t) t ∧ x' t = G (x t) ∧ x 0 = x₀)) := by sorry
