
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Set.Intervals.Basic

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)
variable (ε : ℝ)
variable (ε_pos : ε > 0)

def x_N : ℕ → E
| 0 => x₀
| T + 1 => x_N T + ε • F (x_N T)

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

noncomputable def N (t : ℝ) :=
  ⌊t / ε⌋₊

noncomputable def lam (t : ℝ) :=
  (t - N ε t) / ε

noncomputable def y (t : ℝ) :=
  x_N F x₀ ε (N ε t)

noncomputable def x (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact y F x₀ ε t + (lam₀ * ε) • F (x_N F x₀ ε N₀)

noncomputable def x' (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact (1 - lam₀) • x_N F x₀ ε N₀ + lam₀ • x_N F x₀ ε (N₀ + 1)

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
  rw [x]
  norm_cast
  rw [h₀]
  have h₁ : lam 1 half = half := by
    simp [lam, h₀]
  simp [x_N, h₀, h₁, y]

example : ⌊3 / (2 : ℝ)⌋₊ = 1 := by sorry

lemma floorUncast (k : ℕ) : ⌊(k : ℝ)⌋₊ = k := by
  simp

#check add_smul
  -- [← left_distrib]
  -- norm_num
  -- simp [Nat.floor]
  -- norm_num

#check eq_add_of_sub_eq

open intervalIntegral

#check integral_smul_const

lemma piecewise_constant_ode : ∀ N : ℕ, y F x₀ ε (N*ε) = x₀ + ∫ (s : ℝ) in (0)..(N*ε), F (y F x₀ ε s) ∂volume := by
  intro N
  induction' N with k Ik
  · simp [y, N, x_N]
  · simp
    have NSimp : ∀ n : ℕ, N ε (n * ε) = n := by
      intro n
      simp [N]
      rw [mul_div_cancel]
      simp
      linarith
    calc
    y F x₀ ε ((↑k + 1) * ↑ε) = x_N F x₀ ε k + ε • F (x_N F x₀ ε k) := by
      rw [y]
      norm_cast
      rw [NSimp, x_N]
    _ = y F x₀ ε (k*ε) + ε • F (y F x₀ ε (k*ε)) := by
      rw [y, NSimp]
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s)) + ε • F (y F x₀ ε (k*ε)) := by
      rw [Ik]
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s)) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), (1 : ℝ)) • F (y F x₀ ε (k*ε)) := by
      rw [integral_const]
      simp
      ring_nf
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s)) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), F (y F x₀ ε (k*ε))) := by
      let f (s : ℝ) := (1 : ℝ)
      have tmp : ∀ s, f s = 1 := by intro s; rfl
      have : (∫ (s : ℝ) in (k*ε)..((k+1)*ε), (1 : ℝ)) = (∫ (s : ℝ) in (k*ε)..((k+1)*ε), f s) := by
        -- rw [tmp]
        sorry
      -- rw [this, ← integral_smul_const]
      sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..(k*ε), F (y F x₀ ε s) ∂volume) + (∫ (s : ℝ) in (k*ε)..((k+1)*ε), F (y F x₀ ε s) ∂volume) := by sorry
    _ = x₀ + (∫ (s : ℝ) in (0)..((k+1)*ε), F (y F x₀ ε s) ∂volume) := by sorry

#check abs (α := ℝ)
#check norm

variable (r : ℝ)

#check |r|

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

lemma Claim1 : ∀ (ε : ℝ) (e_pos : ε > 0) (t₀ t₁ : ℝ), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by sorry

lemma pre_Claim1' : ∀ (m k : ℕ), ‖(x_N F x₀ ε (k + m)) - (x_N F x₀ ε m)‖ ≤ M * ε * k := by
  intros m k
  induction' k with k iH
  simp
  rw [Nat.succ_eq_add_one]
  have : k + 1 + m = k + m + 1 := by ring
  rw [this, x_N]
  -- have : x_N F x₀ ε (k + m) + ε • F (x_N F x₀ ε (k + m)) - x_N F x₀ ε m
  --   = x_N F x₀ ε (k + m) - x_N F x₀ ε m + ε • F (x_N F x₀ ε (k + m)) :=
  rw [add_comm, ← add_sub]
  calc
    ‖ε • F (x_N F x₀ ε (k + m)) + (x_N F x₀ ε (k + m) - x_N F x₀ ε m)‖
      ≤ ‖ε • F (x_N F x₀ ε (k + m))‖ + ‖x_N F x₀ ε (k + m) - x_N F x₀ ε m‖ := by
      apply norm_add_le
    _ ≤ ‖ε • F (x_N F x₀ ε (k + m))‖ + M * ε * k := by
      apply add_le_add_left
      exact iH
    _ ≤ M * ε + M * ε * k := by
      rw [norm_smul_of_nonneg]
      specialize F_bdd (x_N F x₀ ε (k + m))
      apply add_le_add_right
      rw [mul_comm]
      rw [mul_le_mul_right]
      exact F_bdd
      exact ε_pos
      linarith
    _ = M * ε * ((k : ℝ) + 1) := by ring
    _ = _ := by norm_cast
  
  -- intros m n m_le_n
  -- let k := n - m
  -- have this₀ : n = k + m := by
  --   simp
  --   symm
  --   apply Nat.sub_add_cancel
  --   assumption
  -- have this₁ : n - m = k := by rfl
  -- norm_cast
  -- rw [this₁, this₀]
  -- induction' k with k iH
  -- simp
  

lemma pre_Claim1'' (ε : ℝ) (e_pos : ε > 0) (t₀ t₁ : ℝ) (t0_le_t1 : t₀ ≤ t₁) : ‖x' F x₀ ε t₁ - x' F x₀ ε t₀‖ ≤ M * (t₁ - t₀) := by
  let N₀ := N ε t₀
  let N₁ := N ε t₁
  let m := N₀ + 1
  cases' lt_or_le t₁ (m : ℝ) with h h
  . have N01 : N₀ = N₁ := by
      sorry
    sorry
  sorry

#check Claim1
