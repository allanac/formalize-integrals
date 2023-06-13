import EulersMethod.Defs

open MeasureTheory
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)


#check abs (α := ℝ)
#check norm

variable (r : ℝ)

#check |r|



lemma Claim1 : ∀ (ε : NNReal) (t₀ t₁ : ℝ), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by
  intro ε t₀ t₁
  calc
    ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ = 
     ‖ x₀ + (∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) - x₀ - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) )‖ := by sorry
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (-∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s))‖ := by rw[← sub_eq_add_neg] ; simp
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (∫ (s : ℝ) in (t₁)..(0), F (y F x₀ ε s) )‖ := by rw[←intervalIntegral.integral_symm ]
    _ = ‖(∫ (s : ℝ) in (t₁)..(t₀), F (y F x₀ ε s) )‖ := by
        rw [add_comm,intervalIntegral.integral_add_adjacent_intervals] 
        
    _ ≤ M * abs (t₀ - t₁) := by rw[intervalIntegral.norm_integral_le_of_norm_le_const]