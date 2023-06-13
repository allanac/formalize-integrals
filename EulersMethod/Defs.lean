
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Set.Intervals.Basic

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
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

noncomputable def y (ε : NNReal) (t : ℝ) :=
  x_N F x₀ ε (N ε t)

noncomputable def x (ε : NNReal) (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact y F x₀ ε t + (lam₀ * ε) • F (x_N F x₀ ε N₀)

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
  simp [x_N, h₀, h₁, y]

#check add_smul
  -- [← left_distrib]
  -- norm_num
  -- simp [Nat.floor]
  -- norm_num

#check deriv

lemma piecewise_constant_ode : ∀ N : ℕ, y F x₀ ε (N*ε) = x₀ + ∫ (s : ℝ) in (0)..(N*ε), F (y F x₀ ε s) ∂volume := by
  intro N
  induction' N with k Ik
  · simp [y, N, x_N]
  · simp [y, N]
    calc
    _ = x_N F x₀ ε k + ε • F (x_N F x₀ ε k) := by sorry
    _ = y F x₀ ε (k*ε) + ε • F (y F x₀ ε (k*ε)) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s) ∂volume) + ε • F (y F x₀ ε (k*ε)) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s) ∂volume) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), (1 : ℝ) ∂volume) • F (y F x₀ ε (k*ε)) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s) ∂volume) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), F (y F x₀ ε (k*ε)) ∂volume) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s) ∂volume) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), F (y F x₀ ε s) ∂volume) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..((k+1)*ε), F (y F x₀ ε s) ∂volume) := by sorry

#check abs (α := ℝ)
#check norm

variable (r : ℝ)

#check |r|

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

#check sub_eq_add_neg

open MeasureTheory

lemma Claim1 : ∀ (ε : NNReal) (t₀ t₁ : ℝ), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by
  intro ε t₀ t₁
  calc
    ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ = ‖ x₀ + (∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ∂volume) - x₀ - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) ∂volume)‖ := by sorry
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ∂volume) - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) ∂volume)‖ := by simp
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ∂volume) + (∫ (s : ℝ) in (t₁)..(0), F (y F x₀ ε s) ∂volume)‖ := by rw [←intervalIntegral.integral_symm]
    _ = ‖(∫ (s : ℝ) in (t₀)..(t₁), F (y F x₀ ε s) ∂volume)‖ := by rw [intervalIntegral.integral_add_adjacent_intervals]
    _ ≤ M * abs (t₀ - t₁) := by rw [intervalIntegral.norm_integral_le_of_norm_le_const]
  
 
#check Claim1
