import EulersMethod.Defs
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open MeasureTheory
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)
variable (ε : ℝ)
variable (ε_pos : 0 < ε)

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)


#check abs (α := ℝ)
#check norm
#check Set.Ico

private def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)

#check max
#check max_eq_right_of_lt
theorem max_eq_right_of_le {α} [LinearOrder α] {a b : α} : a ≤ b → max a b = b := by
  intro h
  rcases eq_or_lt_of_le h with (_ | h)
  simp; assumption
  exact max_eq_right_of_lt h

#check Nat.floor_lt_ceil_of_lt_of_pos

theorem floor_le_ceil_of_le {a b : ℝ} : a ≤ b → ⌊a⌋₊ ≤ ⌈b⌉₊ := by
  intro h
  rcases lt_or_le 0 b with (bpos | bnp)
  rcases lt_or_eq_of_le h with (h | h)
  apply le_of_lt
  apply Nat.floor_lt_ceil_of_lt_of_pos
  assumption
  assumption
  rw [h]
  apply Nat.floor_le_ceil
  have : ⌊a⌋₊ = 0 := by
    simp
    calc
    a ≤ b := h
    _ ≤ 0 := bnp
    _ < _ := by norm_num
  rw [this]
  apply zero_le

#check |r|
theorem my_integrable_congr {EE : Type _} [NormedAddCommGroup EE] {f g: ℝ → EE} {a : ℝ} {b : ℝ} {μ : MeasureTheory.Measure ℝ} (he : Set.EqOn f g (Set.Ico a b)) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable f μ a b := by sorry

lemma Fy_measurable : ∀ (t₁ t₀ ε : ℝ) (_ : 0 < ε) (_ : t₁ ≤ t₀) (_ : 0 ≤ t₁), IntervalIntegrable (fun (s : ℝ) => F (y F x₀ ε s)) volume t₁ t₀ := by
  intro t₁ t₀ ε epos htt hlb
  have enn : 0 ≤ ε := by linarith
  -- rcases lt_or_eq_of_le htt' with (htt | htt)
  let a := Nat.floor (t₁/ε)
  let b := Nat.ceil (t₀/ε)
  have subset_t : Set.uIoc t₁ t₀ ⊆ (Set.uIoc (a*ε) (b*ε) ) := by
    apply Set.Ioc_subset_Ioc
    · apply min_le_of_left_le
      rw [min_eq_left_iff.mpr (htt)]
      simp
      rw [← div_le_div_right epos, mul_div_cancel]
      apply Nat.floor_le
      apply div_nonneg hlb
      apply le_of_lt epos
      apply ne_of_gt epos
    · rw [max_eq_right_of_le htt]
      apply le_trans _ (le_max_right _ (b*ε))
      simp
      rw [← div_le_div_right epos, mul_div_cancel]
      apply Nat.le_ceil
      apply ne_of_gt epos
  apply IntervalIntegrable.mono_set' _ subset_t
  have : a * ε = meas_a ε a:= by rfl
  rw [this]
  -- have tie := Nat.floor_le_ceil_of_le (div_lt_div_of_lt epos htt) (div_pos (lt_of_le_of_lt hlb htt) epos)
  have tie : ⌊t₁ / ε⌋₊ ≤ ⌈t₀ / ε⌉₊ := floor_le_ceil_of_le (div_le_div_of_le enn htt)
  have : b * ε = meas_a ε b := by rfl
  rw [this]
  apply IntervalIntegrable.trans_iterate_Ico
  · norm_num
    linarith
  intro k hk
  rw [meas_a, meas_a]
  let h := (fun (_ : ℝ) => F (y F x₀ ε (k*ε)))
  let f := (fun (s : ℝ) => F (y F x₀ ε s))
  have y_const : ∀ s ∈ Set.Ico (k*ε) ((k+1)*ε), f s = h s := by
    intro s hs
    have hse : s/ε ∈ Set.Ico (k : ℝ) (k+1 : ℝ) := by
      simp at *
      rw [← mul_le_mul_right epos]
      rw [div_mul_cancel]
      rw [← mul_lt_mul_right epos]
      rw [div_mul_cancel]
      tauto
      apply ne_of_gt epos
      apply ne_of_gt epos
    simp
    rw [y,y,N,N]
    rw [mul_div_cancel]
    rw [Nat.floor_eq_on_Ico _ _ hse]
    rw [Nat.floor_coe]
    apply ne_of_gt epos
  have : Set.EqOn f h (Set.Ico (k*ε) ((k+1)*ε)) := y_const
  have g_integrable : IntervalIntegrable h volume (k*ε) ((k+1)*ε) := by 
    apply intervalIntegrable_const
  have more_bullshit := my_integrable_congr this g_integrable
  simp at *
  exact more_bullshit

lemma Fy_measurable' : ∀ (t₁ t₀ ε : ℝ) (_ : 0 < ε) (_ : 0 ≤ t₀) (_ : 0 ≤ t₁), IntervalIntegrable (fun (s : ℝ) => F (y F x₀ ε s)) volume t₁ t₀ := by
  intros t₁ t₀ ε ε_pos t0nn t1nn
  rcases le_total t₀ t₁ with (h01 | h10)
  symm
  apply Fy_measurable <;> assumption
  apply Fy_measurable <;> assumption

#check Fy_measurable

lemma ftc_on_x_bdd : ∀ (N₀ : ℕ) t, 0 ≤ t → t ≤ N₀ * ε → x F x₀ ε t - x₀ = ∫ (s : ℝ) in (0)..(t), F (y F x₀ ε s) := by
  intro N₀
  induction' N₀ with N₀ ih
  intro t tnn tnp
  simp at tnp
  have : t = 0 := by linarith
  rw [this]
  simp [x]
  unfold x_N
  have : N ε 0 = 0 := by
    unfold N
    simp
  rw [this]
  simp
  left; left
  unfold lam
  simp [this]
  intro t tnn tub
  rcases le_or_lt t (N₀ * ε) with (tub' | tlb)
  . specialize ih t tnn tub'
    exact ih
  specialize ih (N₀ * ε) _ _
  apply mul_nonneg
  simp
  linarith
  linarith
  have : x F x₀ ε t - x₀ = (x F x₀ ε t - x F x₀ ε (↑N₀ * ε)) + (x F x₀ ε (↑N₀ * ε) - x₀) := by simp
  rw [this, ih]
  have : (∫ (s : ℝ) in (0)..(t), F (y F x₀ ε s)) = (∫ (s : ℝ) in (N₀ * ε)..(t), F (y F x₀ ε s)) + (∫ (s : ℝ) in (0)..(N₀ * ε), F (y F x₀ ε s)) := by
    -- intervalIntegral
    rw [add_comm, intervalIntegral.integral_add_adjacent_intervals]
    apply Fy_measurable
    exact ε_pos
    apply mul_nonneg
    simp
    linarith
    norm_num
    apply Fy_measurable
    apply ε_pos
    apply le_of_lt tlb
    apply mul_nonneg
    norm_num
    exact le_of_lt ε_pos
  rw [this]
  rw [add_right_cancel_iff]
  symm
  have h₀ : t ∈ closed_ival N₀ ε := by
    constructor
    linarith
    simp at tub
    assumption
  have h₁ : N₀ * ε ∈ closed_ival N₀ ε := by
    constructor
    simp
    apply mul_le_mul_of_nonneg_right
    norm_num
    linarith
  rw [← x_cong_x_alt_closed (th := h₀), ← x_cong_x_alt_closed (th := h₁)]
  unfold intervalIntegral
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have : Set.Ioc t (N₀ * ε) = ∅ := by
    rw [Set.Ioc_eq_empty_iff]
    linarith
  rw [this]
  simp
  have : (∫ (t : ℝ) in Set.Ioo (↑N₀ * ε) t, F (y F x₀ ε t)) = (∫ (_ : ℝ) in (↑N₀ * ε)..(t), F (x_N F x₀ ε N₀)) :=
    calc
      (∫ (t : ℝ) in Set.Ioo (↑N₀ * ε) t, F (y F x₀ ε t)) = (∫ (_ : ℝ) in Set.Ioo (↑N₀ * ε) t, F (x_N F x₀ ε N₀)) := by
        apply MeasureTheory.set_integral_congr
        simp
        intro u uh
        dsimp
        have ug : u ∈ good_ival N₀ ε := by
          apply Set.Ioo_subset_Ioo_right _ uh
          simp at tub
          exact tub
        rw [y_eq_xN_of_good _ _ _ ε_pos ug]
      _ = _ := by
        unfold intervalIntegral
        rw [this]
        simp
  rw [this]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := x_alt F x₀ ε N₀)
  intro v _
  apply deriv_x_alt_eq
  exact ε_pos
  apply intervalIntegrable_const
  exact ε_pos
  exact ε_pos
  -- apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := x_alt F x₀ ε N₀)
  -- exact tlb
  -- intro u uh
  -- apply deriv_x_alt_eq
  -- apply ε_pos
  -- apply le_trans (b := N₀ * ε)
  -- apply nat_ep_nonneg ε_pos
  -- rw [Set.mem_Ioo] at uh
  -- apply le_of_lt uh.left
  -- apply not_bad_of_good (N₀ := N₀)
  -- rcases uh with ⟨ulb, uub⟩
  -- apply Set.mem_Ioo.mpr; refine' ⟨ulb, _⟩
  -- apply lt_of_lt_of_le uub
  -- simp at tub
  -- assumption
  -- apply Fy_measurable
  -- apply ε_pos
  -- apply le_of_lt tlb
  -- apply nat_ep_nonneg ε_pos

lemma ftc_on_x : ∀ t, 0 ≤ t → x F x₀ ε t - x₀ = ∫ (s : ℝ) in (0)..(t), F (y F x₀ ε s) := by
  intro t tnn
  let N₀ : ℕ := ⌈t / ε⌉₊
  have : t ≤ N₀ * ε := by
    have : Eq N₀ ⌈t / ε⌉₊ := by rfl
    rw [this]
    have : t = t / ε * ε := by
      symm
      apply div_mul_cancel
      linarith
    rw [this]
    apply mul_le_mul_of_nonneg_right
    rw [← this]
    apply Nat.le_ceil
    linarith
  apply ftc_on_x_bdd
  exact ε_pos
  exact tnn
  exact this

lemma Claim1 : ∀ (ε : ℝ) (_ : 0 < ε) (t₀ t₁ : ℝ) (_ : 0 ≤ t₁) (_ : 0 ≤ t₀), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by
  intro ε epos t₀ t₁ t1nn t0nn
  calc
    ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ = 
     ‖ x₀ + (∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) - x₀ - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) )‖ := by
      have : x F x₀ ε t₀ - x F x₀ ε t₁ = (x F x₀ ε t₀ - x₀) - (x F x₀ ε t₁ - x₀) := by simp
      rw [this, ftc_on_x, ftc_on_x]
      simp
      exact epos
      exact t1nn
      exact epos
      exact t0nn
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (-∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s))‖ := by rw[← sub_eq_add_neg] ; simp
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (∫ (s : ℝ) in (t₁)..(0), F (y F x₀ ε s) )‖ := by rw[←intervalIntegral.integral_symm ]
    _ = ‖(∫ (s : ℝ) in (t₁)..(t₀), F (y F x₀ ε s) )‖ := by
        rw [add_comm,intervalIntegral.integral_add_adjacent_intervals] 
        · apply IntervalIntegrable.symm
          apply Fy_measurable F x₀ 0 t₁ ε epos t1nn (le_refl 0)
        · apply Fy_measurable F x₀ 0 t₀ ε epos t0nn (le_refl 0)
    _ ≤ M * abs (t₀ - t₁) := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro _ _
      apply F_bdd

#check Claim1
