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

private def meas_a (ε : ℝ) (k : ℕ) : ℝ := k*ε

variable (r : ℝ)

#check |r|
theorem my_integrable_congr {EE : Type _} [NormedAddCommGroup EE] {f g: ℝ → EE} {a : ℝ} {b : ℝ} {μ : MeasureTheory.Measure ℝ} (he : Set.EqOn f g (Set.Ico a b)) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable f μ a b := by sorry

lemma Fy_measurable : ∀ (t₁ t₀ ε : ℝ) (_ : 0 < ε) (_ : t₁ < t₀) (_ : 0 ≤ t₁), IntervalIntegrable (fun (s : ℝ) => F (y F x₀ ε s)) volume t₁ t₀ := by
  intro t₁ t₀ ε epos htt hlb
  let a := Nat.floor (t₁/ε)
  let b := Nat.ceil (t₀/ε)
  have subset_t : Set.uIoc t₁ t₀ ⊆ (Set.uIoc (a*ε) (b*ε) ) := by
    apply Set.Ioc_subset_Ioc
    · apply min_le_of_left_le
      rw [min_eq_left_iff.mpr (le_of_lt htt)]
      simp
      rw [← div_le_div_right epos, mul_div_cancel]
      apply Nat.floor_le
      apply div_nonneg hlb
      apply le_of_lt epos
      apply ne_of_gt epos
    · rw [max_eq_right_of_lt htt]
      apply le_trans _ (le_max_right _ (b*ε))
      simp
      rw [← div_le_div_right epos, mul_div_cancel]
      apply Nat.le_ceil
      apply ne_of_gt epos
  apply IntervalIntegrable.mono_set' _ subset_t
  have : a * ε = meas_a ε a:= by rfl
  rw [this]
  have tie :=Nat.floor_lt_ceil_of_lt_of_pos (div_lt_div_of_lt epos htt) (div_pos (lt_of_le_of_lt hlb htt) epos)
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

#check Fy_measurable

lemma Claim1 : ∀ (ε : ℝ) (_ : 0 < ε) (t₀ t₁ : ℝ) (_ : 0 < t₁) (_ : 0 < t₀), ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ ≤ M * |t₀ - t₁| := by
  intro ε epos t₀ t₁ t1pos t0pos
  calc
    ‖x F x₀ ε t₀ - x F x₀ ε t₁‖ = 
     ‖ x₀ + (∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) - x₀ - (∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s) )‖ := by sorry
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (-∫ (s : ℝ) in (0)..(t₁), F (y F x₀ ε s))‖ := by rw[← sub_eq_add_neg] ; simp
    _ = ‖(∫ (s : ℝ) in (0)..(t₀), F (y F x₀ ε s) ) + (∫ (s : ℝ) in (t₁)..(0), F (y F x₀ ε s) )‖ := by rw[←intervalIntegral.integral_symm ]
    _ = ‖(∫ (s : ℝ) in (t₁)..(t₀), F (y F x₀ ε s) )‖ := by
        rw [add_comm,intervalIntegral.integral_add_adjacent_intervals] 
        · apply IntervalIntegrable.symm
          apply Fy_measurable F x₀ 0 t₁ ε epos t1pos (le_refl 0)
        · apply Fy_measurable F x₀ 0 t₀ ε epos t0pos (le_refl 0)
    _ ≤ M * abs (t₀ - t₁) := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro _ _
      apply F_bdd

#check Claim1
