import EulersMethod.Defs

open MeasureTheory
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)


#check abs (α := ℝ)
#check norm
#check Set.Ico

def meas_a (ε t₀ t₁ : ℝ) (m₀ n₀ : ℕ) (k : ℕ) : ℝ :=
if k = m₀ then 
  t₁
else if k = n₀ then
  t₀
else
  k*ε

variable (r : ℝ)

#check |r|


lemma Fy_measurable : ∀ (t₁ t₀  : ℝ), IntervalIntegrable (fun s => F (y F x₀ ε s)) volume t₁ t₀ := by
  intro t₁ t₀
  have : t₁ = meas_a ε t₀ t₁ (Nat.floor t₁) (Nat.ceil t₀) (Nat.floor t₁) := by sorry
  rw [this]
  have : t₀ = meas_a ε t₀ t₁ (Nat.floor t₁) (Nat.ceil t₀) (Nat.ceil t₀) := by sorry
  nth_rw 3 [this]
  apply IntervalIntegrable.trans_iterate_Ico
  sorry
  sorry

#check Fy_measurable

lemma Claim1 : ∀ (ε : NNReal) (t₀ t₁ : ℝ), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by
  intro ε t₀ t₁
  calc
    ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ = 
     ‖ x₀ + (∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) - x₀ - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) )‖ := by sorry
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (-∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s))‖ := by rw[← sub_eq_add_neg] ; simp
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (∫ (s : ℝ) in (t₁)..(0), F (y F x₀ ε s) )‖ := by rw[←intervalIntegral.integral_symm ]
    _ = ‖(∫ (s : ℝ) in (t₁)..(t₀), F (y F x₀ ε s) )‖ := by
        rw [add_comm,intervalIntegral.integral_add_adjacent_intervals] 
        · apply Fy_measurable
        · apply Fy_measurable
    _ ≤ M * abs (t₀ - t₁) := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro _ _
      apply F_bdd
