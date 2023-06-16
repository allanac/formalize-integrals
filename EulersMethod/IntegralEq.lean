
import EulersMethod.Claim2
import EulersMethod.ExLimit
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped BoundedContinuousFunction

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E →ᵇ E)
variable (x₀ : E)

variable {M : NNReal}
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

section

-- Theorems to be proven in Claim 3:

-- (x F x₀ ε) '' Set.Icc 0 1

noncomputable def x_L' := fun (t : ℝ) => x_L F x₀ (Set.projIcc 0 1 (by norm_num) t)
-- noncomputable def x_L'' (k : ℕ) : ℝ →ᵇ E where
--   toFun := x_L'f F x₀ k
--   map_bounded' := by
    
--     sorry
--   continuous_toFun := sorry

noncomputable def x_c₀ (k : ℕ) := fun (t : ℝ) => x_c F x₀ k (Set.projIcc 0 1 (by norm_num) t)
noncomputable def y_c₀ (k : ℕ) := fun (t : ℝ) => y_c F x₀ k (Set.projIcc 0 1 (by norm_num) t)

variable (G : Filter (ℝ →ᵇ E))
#check lim G

lemma int_lim_eq_lim_int {a b : ℝ} {f : ℝ →ᵇ E} {F : (ℕ → ℝ → E)}
  (h : TendstoUniformly F f (Filter.atTop))
  : Filter.Tendsto (fun n => (∫ (s : ℝ) in (a)..(b), F n s))
    (Filter.atTop)
    (nhds (∫ (s : ℝ) in (a)..(b), f s))
  := by

  sorry

#print y_c
#check ContinuousMap.toFun_eq_coe

lemma x_eq_integ_seq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc 0 1 → x_c₀ F x₀ k t = x₀ + ∫ (s : ℝ) in (0)..(t), F (y_c₀ F x₀ k s) := by
  intro k t th
  have : x_c₀ F x₀ k t = x₀ + (x_c₀ F x₀ k t - x₀) := by simp
  rw [this]
  -- rw [x_c₀, x_c]
  -- rw [BoundedContinuousFunction.continuous_coe]
  -- unfold ContinuousMap
  -- dsimp
  have : ∀ t : ℝ, t ∈ (Set.Icc 0 1 : Set ℝ) → x_c₀ F x₀ k t = x F x₀ (1 / (↑k + 1)) t := by
    intro t th
    unfold x_c₀ 
    rw [← BoundedContinuousFunction.coe_to_continuous_fun]
    unfold x_c x_c'
    dsimp
    rw [Set.projIcc_val _ ⟨t, th⟩]
  specialize this t th
  rw [this]
  have : ∀ s : ℝ, s ∈ Set.Icc 0 t → F (y_c₀ F x₀ k s) = F (y F x₀ (1 / (↑k + 1)) s) := by
    intro s sh
    rw [y_c₀, y_c]
    dsimp
    have : ↑(Set.projIcc 0 1 y_c₀.proof_1 s) = s := by
      unfold Set.projIcc
      dsimp
      rw [max_eq_right, min_eq_right]
      apply le_trans sh.2 th.2
      rw [min_eq_right]
      exact sh.1
      apply le_trans sh.2 th.2
    rw [this]
  have : Set.EqOn (fun s => F (y_c₀ F x₀ k s)) (fun s => F (y F x₀ (1 / (↑k + 1)) s)) (Set.uIcc 0 t) := by
    intro s sh
    apply this
    rw [Set.uIcc_of_le] at sh
    assumption
    exact th.1
  rw [intervalIntegral.integral_congr this]
  rw [ftc_on_x]
  norm_cast
  norm_num
  norm_cast
  norm_num
  exact th.1

theorem xL_eq_integ : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
    x_L' F x₀ t
      = x₀ + (∫ (s : ℝ) in (0)..(t), F (x_L' F x₀ s)) :=
  by
  intro t th
  sorry
