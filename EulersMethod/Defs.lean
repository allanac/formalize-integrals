import Mathlib.Analysis.NormedSpace.Basic

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : E → E)
variable (x₀ : E)

noncomputable def x (ε : NNReal) : ℕ → E
| 0 => x₀
| T + 1 => x ε  T + ε • F (x ε T)

example : x F x₀ 1 0 = x₀ := rfl

example : x F x₀ 1 1 = x₀ + F x₀ := by
  rw [x]
  simp
  rw [x]

example : x F x₀ 1 2 = x₀ + F x₀ + F (x₀ + F x₀) := by
  rw [x,x,x]
  simp
