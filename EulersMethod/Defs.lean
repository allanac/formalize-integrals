
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)
variable (ε : ℝ)
variable (ε_pos : 0 < ε)

def x_N (ε : ℝ) : ℕ → E
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

noncomputable def N (ε : ℝ) (t : ℝ) :=
  ⌊t / ε⌋₊

noncomputable def lam (ε : ℝ) (t : ℝ) :=
  (t - N ε t) / ε

noncomputable def y (ε : ℝ) (t : ℝ) :=
  x_N F x₀ ε (N ε t)

noncomputable def x (ε : ℝ) (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact y F x₀ ε t + (lam₀ * ε) • F (x_N F x₀ ε N₀)

-- noncomputable def x (ε : \R) : ℝ → E := by
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

-- #check deriv

open MeasureTheory

#check MeasureTheory.MeasureSpace.volume

noncomputable def μ : MeasureTheory.Measure ℝ := MeasureTheory.MeasureSpace.volume

def NNR_Set : Set ℝ := fun (r : ℝ) => 0 ≤ r
def NNR_Subtype := NNR_Set
noncomputable def μ₀ : Measure NNR_Set := volume

-- instance : NontriviallyNormedField NNR_Set where
--   non_trivial := sorry

#check deriv (x F x₀ ε) =ᵐ[μ₀] y F x₀ ε

-- lemma deriv_x_eqae_y : deriv (x F x₀ ε) =ᵐ[μ₀] y F x₀ ε := by
--   rw [Filter.EventuallyEq, Filter.Eventually]
--   sorry

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
