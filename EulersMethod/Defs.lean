
import Mathlib.Analysis.NormedSpace.Basic

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : E → E)
variable (x₀ : E)

def x_N (ε : NNReal) : ℕ → E
| 0 => x₀
| T + 1 => x_N ε T + ε • F (x_N ε T)

example : x_N F x₀ 1 0 = x₀ := rfl

example : x_N F x₀ 1 1 = x₀ + F x₀ := by
  rw [x_N]
  simp
  rw [x_N]

example : x_N F x₀ 1 2 = x₀ + F x₀ + F (x₀ + F x₀) := by
  simp [x_N]

open Int

#check x_N

-- def x_Z (ε : NNReal) : ℤ → E
-- | ofNat n => x_N F x₀ ε n
-- | negSucc _ => x₀

#print Int

#check Nat.floor (1/(2 : ℝ))

noncomputable def x (ε : NNReal) : ℝ → E := by
  intro t
  let N : ℕ := Nat.floor (t / ε)
  let l : ℝ := (t - N) / ε
  exact (1 - l) • (x_N F x₀ ε N) + l • (x_N F x₀ ε (N + 1))

noncomputable def half := (1 / (2 : ℝ))

example : Nat.floor half = 0 := by
  simp
  rw [half]
  norm_num

example : x F x₀ 1 (half : ℝ) = x₀ + half • F (x₀) := by
  have : Nat.floor (half / (1 : NNReal)) = 0 := by
    simp [half]
    norm_num
  rw [x, this]
  simp [x_N]
  simp [add_comm]
  rw [add_comm (half • x₀), add_assoc, ← add_smul]
  norm_num
  apply add_comm
#check add_smul
  -- [← left_distrib]
  -- norm_num
  -- simp [Nat.floor]
  -- norm_num
