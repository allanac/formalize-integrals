import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
import EulersMethod.ExLimit
--import Std.Tactic.Infer

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem peano_existance_F_bdd (G : E →ᵇ E) (x₀ : E) :
  ∃ (δ : ℝ), δ > 0 ∧ (∃ x : ℝ → E,  (∃ x' : ℝ → E,
    Continuous x' ∧ ∀ t ∈ Set.Icc (0:ℝ) δ, HasDerivWithinAt x (x' t) (Set.Icc 0 δ) t ∧ x' t = G (x t) ∧ x 0 = x₀)) := by sorry
