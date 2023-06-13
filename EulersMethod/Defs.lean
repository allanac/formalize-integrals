
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal

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

-- open Int

#check x_N

-- def x_Z (ε : NNReal) : ℤ → E
-- | ofNat n => x_N F x₀ ε n
-- | negSucc _ => x₀

#print Int

#check Nat.floor (1/(2 : ℝ))
#check ⌊1 / (2 : ℝ)⌋₊
#check 1 / 2

noncomputable def N (ε : NNReal) (t : ℝ) :=
  ⌊t / ε⌋₊

noncomputable def lam (ε : NNReal) (t : ℝ) :=
  (t - N ε t) / ε

noncomputable def x (ε : NNReal) (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact (1 - lam₀) • (x_N F x₀ ε N₀) + lam₀ • (x_N F x₀ ε (N₀ + 1))

-- noncomputable def x (ε : NNReal) : ℝ → E := by
--   intro t
--   let N : ℕ := Nat.floor (t / ε)
--   let l : ℝ := (t - N) / ε
--   exact (1 - l) • (x_N F x₀ ε N) + l • (x_N F x₀ ε (N + 1))

-- example : x F x₀ = x' F x₀ := by rfl

noncomputable def half := (1 / (2 : ℝ))

example : Nat.floor half = 0 := by
  simp
  rw [half]
  norm_num

example : x F x₀ 1 (half : ℝ) = x₀ + half • F (x₀) := by
  have h₀ : N 1 half = 0 := by
    simp [N, half]
    norm_num
  rw [x, h₀]
  have h₁ : lam 1 half = half := by
    simp [lam, h₀]
  simp [x_N, h₀, h₁]
  simp [add_comm]
  rw [add_comm (half • x₀), add_assoc, ← add_smul]
  norm_num
  apply add_comm

noncomputable def y (ε : NNReal) (t : ℝ) :=
  x_N F x₀ ε (N ε t)

#check add_smul
  -- [← left_distrib]
  -- norm_num
  -- simp [Nat.floor]
  -- norm_num

#check abs (α := ℝ)
#check norm

variable (r : ℝ)

#check |r|

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

lemma Claim1 : ∀ (ε : NNReal) (t₀ t₁ : ℝ), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := sorry

#check Claim1