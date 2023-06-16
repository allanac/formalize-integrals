
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Topology.Order.Basic
-- import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.MetricSpace.Lipschitz
-- import Mathlib.Topology.MetricSpace.EMetricSpace
-- import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Analysis.Normed.Group.Basic

-- below theorem is all we needed...
#check LipschitzOnWith.extend_real

--[Rle : LE R] [Rlt : LT R]
variable {R : Type _} [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R]
variable {S : Type _} [TopologicalSpace S]
variable {f : R → S}
variable [PseudoMetricSpace R] [PseudoMetricSpace S]

-- #check ℝ

-- -- def realorder := (inferInstance : Total)

-- #check R

-- #check Decidable

noncomputable def testdecs {a : R} : ∀ t : R, Decidable (Set.Iio a t) := by
  intro t; by_cases h : Set.Iio a t
  . right; exact h
  . left; exact h

#check testdecs

-- noncomputable instance {a : R} : ∀ t : R, Decidable (Set.Iio a t) := testdecs

-- instance (a t : R) : Decidable (t ∈ Set.Iio a) := by
--   rw [Set.mem_Iio]
--   apply drlt (a := t) (b := a)

noncomputable def clamp (f : R → S) (a b : R) :=
  Set.piecewise (Set.Iio a) (fun _ => f a) (
    Set.piecewise (Set.Iic b) (fun t => f t) (
      fun _ => f b
    )
  )

#check Set.ite

theorem clamp_cts {f : R → S} {a b : R} (aleb : a ≤ b) (cts : ContinuousOn f (Set.Icc a b)) : Continuous (clamp f a b) := by
  apply continuous_piecewise
  intro a' ah
  rw [frontier_Iio, Set.mem_singleton_iff] at ah;
  rw [ah]
  . simp [aleb]
  . apply continuousOn_const
  . have : closure (Set.Iio aᶜ) = Set.ite (Set.Iic b) (Set.Icc a b) (Set.Ici a) := by
      simp only [Set.compl_Iio, closure_Ici, ge_iff_le, not_le, gt_iff_lt, Set.ite_left]
      ext x
      constructor
      intro xh
      by_cases xh' : x ≤ b
      . left;
        simp
        tauto
      . right
        simp
        constructor
        exact xh
        push_neg at xh'
        exact xh'
      rintro (r | l)
      exact r.left.left
      exact l.left
    rw [this]
    apply continuousOn_piecewise_ite
    . exact cts
    . intro b bh
      -- rw [frontier_Iic, Set.mem_singleton_iff] at bh
      -- rw [bh]
      apply continuousOn_const
      exact bh
    . ext x
      simp [aleb]
      intro bh _
      rw [bh]
    . intro t th
      simp at th
      have th := th.right
      rw [th]

theorem swap_dist' {a b : R} : dist a b = dist b a := by
  have : dist a b = (Function.swap dist) b a := by rfl
  rw [this]
  rw [swap_dist]

theorem clamp_lipschitz {f : ℝ → S} {a b : ℝ} {M : NNReal}
  (lcts : LipschitzOnWith M f (Set.Icc a b))
  : LipschitzWith M (clamp f a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro t₀ t₁
  -- rw [edist_dist, edist_dist]
  wlog h : t₀ ≤ t₁ with h'
  . rw [swap_dist' (R := ℝ), swap_dist' (R := S)]
    apply h' (R := ℝ)
    . exact lcts
    . push_neg at h
      linarith
    . exact f
  . rw [dist_eq_norm']
    have : 0 ≤ t₁ - t₀ := by linarith
    simp only [Real.norm_eq_abs, ge_iff_le, abs_of_nonneg this]

    sorry
    -- rw [edist_abs]
    -- have this₀ : dist (clamp f a b t₀) (clamp f a b t₁) = dist (clamp f a b t₁) (clamp f a b t₀) := by
    --   simp [swap_dist]
    --   sorry
#check dist_sub_right
