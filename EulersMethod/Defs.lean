
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Filter

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
-- #check 1 / 2

structure fn_dom (α : Type _) (β : Type _) where
  toFun : α → β
  dom : Set α

def fn_dom_rel := fun {α β} (⟨f₁, d₁⟩ : fn_dom α β) (⟨f₂, d₂⟩ : fn_dom α β) =>
  (d₁ = d₂ ∧ ∀ a : d₁, f₁ a = f₂ a)

#check Equiv
#check Equivalence

theorem fn_dom_rfl (fd : fn_dom α β) : fn_dom_rel fd fd := by
  rcases fd with ⟨f, d⟩
  simp [fn_dom_rel]

theorem fn_dom_sym {fd₁ fd₂ : fn_dom α β} : fn_dom_rel fd₁ fd₂ → fn_dom_rel fd₂ fd₁ := by
  rcases fd₁ with ⟨f₁, d₁⟩
  rcases fd₂ with ⟨f₂, d₂⟩
  simp [fn_dom_rel]
  intro d_eq f_eq
  constructor
  apply d_eq.symm
  intro a ah
  rw [← d_eq] at ah
  specialize f_eq a ah
  symm
  assumption

theorem fn_dom_trans {fd₁ fd₂ fd₃ : fn_dom α β} :
  fn_dom_rel fd₁ fd₂ →
  fn_dom_rel fd₂ fd₃ →
    fn_dom_rel fd₁ fd₃ := by
  rcases fd₁ with ⟨f₁, d₁⟩
  rcases fd₂ with ⟨f₂, d₂⟩
  rcases fd₃ with ⟨f₃, d₃⟩
  simp [fn_dom_rel]
  rintro hd12 hf12 hd23 hf23
  constructor
  rw [hd12]; exact hd23
  rintro a ah
  specialize hf12 a ah
  rw [hd12] at ah
  specialize hf23 a ah
  rw [hf12]
  exact hf23

instance : Equivalence (@fn_dom_rel α β) where
  refl := fn_dom_rfl
  symm := fn_dom_sym
  trans := fn_dom_trans

def fn_dom_le {α β}:= fun (⟨f₁, d₁⟩ : fn_dom α β) (⟨f₂, d₂⟩ : fn_dom α β) =>
  d₁ ⊆ d₂ ∧ ∀ a : α, a ∈ d₁ → f₁ a = f₂ a

instance : LE (fn_dom α β) where
  le := fn_dom_le

instance : Preorder (fn_dom α β) where
  le_refl := by
    rintro ⟨f, d⟩
    constructor
    tauto
    intro _ _; rfl
  le_trans := by
    rintro ⟨f₁, d₁⟩ ⟨f₂, d₂⟩ ⟨f₃, d₃⟩
    rintro ⟨hd12, hf12⟩ ⟨hd23, hf23⟩
    constructor
    tauto
    intro a ah
    rw [hf12 a ah]
    rw [hf23 a (hd12 ah)]

theorem fn_dom_le_antisym : ∀ a b : fn_dom α β, a ≤ b → b ≤ a → fn_dom_rel a b := by
  rintro ⟨f₁, d₁⟩ ⟨f₂, d₂⟩ ⟨hd, hf⟩ ⟨hd', _⟩
  simp [fn_dom_rel]
  constructor
  ext
  tauto
  exact hf

-- instance : PartialOrder (fn_dom α β) where
--   le_antisymm := by
--     rintro ⟨f₁, d₁⟩ ⟨f₂, d₂⟩ ⟨hd, hf⟩ ⟨hd', hf'⟩
    


#check PartialOrder

#check LE

#check DifferentiableAt

def fn_dom_univ (f : α → β) := fn_dom.mk f Set.univ

def fn_dom_codom {α β} := fun (⟨f, d⟩ : fn_dom α β) (codom : Set β) =>
  (⟨f, d ∩ f⁻¹' codom⟩ : fn_dom α β)

noncomputable def fn_dom_deriv := fun (⟨f, d⟩ : fn_dom ℝ E) => fn_dom.mk
  (deriv f)
  (d ∩ DifferentiableAt ℝ f)

noncomputable def realFloor (r : ℝ) := (⌊r⌋₊ : ℝ)

#check (Nat.cast : ℕ → ℝ)

theorem deriv_eq_deriv (f g : ℝ → E) (u : Set ℝ) (hu : IsOpen u) : derivWithin f u = derivWithin g u := by
  ext t
  unfold derivWithin
  unfold fderivWithin
  sorry

theorem floorDiffAt : ((Nat.cast : ℕ → ℝ) '' univ)ᶜ ⊆ DifferentiableAt ℝ realFloor := by
  intro x xh
  apply sorry

#check pure

#check (0 : ℝ → ℝ)

noncomputable def N (ε : ℝ) (t : ℝ) :=
  ⌊t / ε⌋₊

example : deriv (fun u => ((N ε u) : ℝ)) = sorry := by
  unfold N
  -- rw [deriv_]
  sorry

noncomputable def lam (ε : ℝ) (t : ℝ) :=
  (t / ε - N ε t)

example : deriv (lam ε) = sorry := by
  unfold lam
  sorry

noncomputable def y (ε : ℝ) (t : ℝ) :=
  x_N F x₀ ε (N ε t)

noncomputable def x (ε : ℝ) (t : ℝ) := by
  let lam₀ := lam ε t
  let N₀ := N ε t
  exact x_N F x₀ ε N₀ + (lam₀ * ε) • F (y F x₀ ε t)

-- def tmp₀ := ℕ * ε

def bad_set := (fun n : ℕ => n * ε) '' Set.univ
#print bad_set

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

#print lam
noncomputable def lam_alt (N₀ : ℕ) (t : ℝ) :=
  (t / ε - N₀)

#print x
noncomputable def x_alt (N₀ : ℕ) (t : ℝ) :=
  x_N F x₀ ε N₀ + ((lam_alt ε N₀ t) * ε) • F (x_N F x₀ ε N₀)

#check HasDerivAt.const_smul
#check HasDerivAt.const_add
#check HasDerivAt.smul_const

#check hasDerivAt_id

theorem deriv_x_alt_eq (N₀ : ℕ) : ∀ t : ℝ, HasDerivAt (x_alt F x₀ ε N₀) (F (x_N F x₀ ε N₀)) t := by
  intro t
  have : F (x_N F x₀ ε N₀) = (1 : ℝ) • F (x_N F x₀ ε N₀) := by simp
  rw [this]
  apply HasDerivAt.const_add
  have : (fun t => (lam_alt ε N₀ t * ε)) = (fun t => t - N₀ * ε):= by --(fun x => lam_alt ε N₀ x * ε) t := by simp
    ext
    unfold lam_alt
    rw [sub_mul]
    rw [div_mul_cancel]
    linarith
  apply HasDerivAt.smul_const
  -- have : (1 : ℝ) = (1 / ε) * ε := by symm; apply div_mul_cancel; linarith
  -- have : (fun t : ℝ => )
  rw [this]
  apply HasDerivAt.sub_const
  apply hasDerivAt_id
  -- rw [this]
  -- let g := fun x => (lam_alt ε N₀ x * ε) • F (x_N F x₀ ε N₀)
  -- have g_eq : g = (fun x => (lam_alt ε N₀ x * ε) • F (x_N F x₀ ε N₀)) := rfl
  -- let c := fun (x : ℝ) => (lam_alt ε N₀ x * ε)
  -- have c_eq : c = fun (x : ℝ) => (lam_alt ε N₀ x * ε) := rfl
  -- let f := F (x_N F x₀ ε N₀)
  -- have f_eq : f = F (x_N F x₀ ε N₀) := rfl
  -- have g_decomp : g = fun y => (c y) • f := rfl
  -- rw [← g_eq, g_decomp, ← f_eq]
  -- apply HasDerivAt.smul_const (c := c) (f := f) (c' := _) (x := t)
  -- apply HasDerivAt.smul_const (c := fun (x : ℝ) => (lam_alt ε N₀ x * ε)) (f := F (x_N F x₀ ε N₀)) (c' := 1) (x := t)

#check HasDerivAt.congr_of_eventuallyEq
#check Filter.mem_of_superset

theorem x_cong_x_alt (N₀ : ℕ) (t : ℝ) (th : (Set.Ioo (N₀ * ε) ((N₀ + 1) * ε) : Set ℝ) t) : x_alt F x₀ ε N₀ =ᶠ[nhds t] x F x₀ ε := by
  let u : Set ℝ := Set.Ioo (N₀ * ε) ((N₀ + 1) * ε)
  apply Filter.mem_of_superset (x := u)
  apply Ioo_mem_nhds
  apply th.left
  apply th.right
  . rintro t ⟨tlb, tub⟩
    simp
    unfold x x_alt
    simp
    have : N ε t = N₀ := by
      rw [N, Nat.floor_eq_iff]
      constructor
      calc
        N₀ = N₀ * ε / ε := by
          symm
          apply mul_div_cancel
          linarith
        _ ≤ _ := by
          rw [div_le_div_right]
          linarith
          assumption
      have : (N₀ + 1) = (N₀ + 1) * ε / ε := by symm; apply mul_div_cancel; linarith
      rw [this]
      rw [div_lt_div_right]
      exact tub
      exact ε_pos
      apply div_nonneg
      apply le_trans (b := N₀ * ε)
      apply mul_nonneg
      simp
      linarith
      linarith
      linarith
    unfold lam y lam_alt
    rw [this]

#print y

#check HasDerivAt
#check HasDerivAt.congr_of_eventuallyEq

theorem der_x_eq_Fy (t : ℝ) : (t ∉ bad_set ε) → (HasDerivAt (x F x₀ ε) (F (y F x₀ ε t)) t) := by
  intro th
  let N₀ := N ε t
  have N0_eq : N₀ = N ε t := rfl
  rcases le_or_lt 0 t with h | h
  . let I : Set ℝ := Set.Ioo (N₀ * ε) ((N₀ + 1) * ε)
    have : t ∈ I := by
      constructor
      rw [N0_eq]
      unfold N
      apply lt_of_le_of_ne
      apply mul_le_of_nonneg_of_le_div
      assumption
      linarith
      apply Nat.floor_le
      apply div_nonneg <;> linarith
      unfold bad_set at th
      rw [Set.mem_image] at th
      push_neg at th
      apply th
      simp
      rw [N0_eq]
      unfold N
      have : t = (t / ε) * ε := by
        rw [div_mul_cancel]
        linarith
      rw [this]
      rw [mul_lt_mul_right]
      rw [← this]
      apply Nat.lt_floor_add_one
      assumption
    unfold y
    apply HasDerivAt.congr_of_eventuallyEq _ (x_cong_x_alt F x₀ ε ε_pos N₀ t this).symm
    rw [← N0_eq]
    apply deriv_x_alt_eq
    exact ε_pos
  . have : N ε t = 0 := by
      unfold N
      simp
      calc
        t / ε < 0 := by
          apply div_neg_of_neg_of_pos <;> assumption
        _ < 1 := by norm_num
    let I : Set ℝ := Set.Iio 0
    have : t ∈ I := by
      rw [Set.mem_Iio]
      exact h
    unfold y
    sorry --apply HasDerivAt.congr_of_eventuallyEq _ (x_cong_x_alt F x₀ ε ε_pos N₀ t this).symm

theorem bad_set_almost_nowhere : volume (bad_set ε) = 0 := by
  sorry

-- instance : NontriviallyNormedField NNR_Set where
--   non_trivial := sorry

#check (fun t => deriv (x F x₀ ε) t) =ᵐ[μ₀] (fun t => y F x₀ ε t)
-- #check deriv (x F x₀ ε) =ᵐ[μ₀] y F x₀ ε

#check ite_ae_eq_of_measure_zero

#check HasDerivAt

#check derivWithin (x F x₀ ε) NNR_Set

example (t : ℝ) : deriv (fun u => x F x₀ ε u) t = sorry := by
  unfold x
  sorry

-- lemma deriv_x_eqae_y : (fun t => deriv (x F x₀ ε) t) =ᵐ[μ₀] (fun t => y F x₀ ε t) := by
--   calc
--     (fun t => deriv (x F x₀ ε) t) =ᵐ[μ₀] (fun t => if sorry)
--   apply ite_ae_eq_of_measure_zero
--   rw [Filter.EventuallyEq]
--   rw [ae_iff_comp]

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
