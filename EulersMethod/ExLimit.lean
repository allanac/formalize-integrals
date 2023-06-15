import EulersMethod.Defs
import EulersMethod.Claim1
import EulersMethod.Claim2
--import Std.Tactic.Infer

-- The xk(·) are uniformly bounded on [0,1]:
-- sup sup |xk(t)| < ∞. k t∈[0,1]

open scoped BoundedContinuousFunction

#check Claim1
#check uniformlyBounded

open MeasureTheory

section

variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)
#where

variable (M : NNReal)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

noncomputable def x_c' (k : ℕ) : (Set.Icc 0 (1 : ℝ)) → E
| t => x F x₀ (1/((k : ℝ)+1)) (t)
open ENNReal
lemma x_is_lipschitz : ∀ (k : ℕ), LipschitzWith M (x_c' F x₀ k) := by
  intro k
  rw [lipschitzWith_iff_dist_le_mul]
  intro z1 z2
  have : M * dist z1 z2 = M * norm ((z1:ℝ)-(z2:ℝ)) := by
    rw [mul_eq_mul_left_iff]
    left
    rfl
  simp
  rw [this]
  rw [x_c',x_c']
  simp
  have := Claim1 F x₀ M F_bdd (1/((k : ℝ)+1)) (one_div_pos.mpr (Nat.cast_add_one_pos _)) z1 z2
  simp at *
  rw [dist_eq_norm]
  apply this
  · rcases z2 with ⟨z2', z2h⟩
    apply (Set.mem_Icc.mp z2h).left
  · rcases z1 with ⟨z1', z1h⟩
    apply (Set.mem_Icc.mp z1h).left

#check x_is_lipschitz F x₀ M
--set_option pp.all true
noncomputable def x_c (k : ℕ) : (Set.Icc 0 (1 : ℝ)) →ᵇ E where
  toFun := x_c' F x₀ k
  map_bounded' := by
    obtain ⟨C, hc⟩ := uniformlyBounded F x₀
    simp
    use 2*C
    intro a ha b hb
    simp
    rw [x_c',x_c']
    norm_num
    rw [dist_eq_norm]
    calc
    _ ≤ ‖x F x₀ (↑k + 1)⁻¹ ↑a‖ + ‖x F x₀ (↑k + 1)⁻¹ ↑b‖ := norm_sub_le _ _
    _ ≤ C + ‖x F x₀ (↑k + 1)⁻¹ ↑b‖ := by
      apply add_le_add_right
      apply hc
      simp
      · apply Nat.cast_add_one_pos
      · tauto
    _ ≤ C + C := by
      apply add_le_add_left
      apply hc
      simp
      · apply Nat.cast_add_one_pos
      · tauto
    _ ≤ 2*C := by linarith
  continuous_toFun := LipschitzWith.continuous (x_is_lipschitz F x₀ M F_bdd k)


#check x_c F x₀ M

#check x


lemma x_c_eq_cont_at  (a : Set.Icc 0 1) : EquicontinuousAt (fun n ↦ (x_c F x₀ M F_bdd n).toFun) a := by sorry
-- use Claim1 here

lemma x_c_eq_cont : Equicontinuous (fun n ↦ (x_c F x₀ M F_bdd n).toFun) := x_c_eq_cont_at F x₀ M F_bdd

def A := Set.range (x_c F x₀ M F_bdd)


#check A

lemma A_is_compact : IsCompact (A F x₀ M F_bdd) := by sorry
-- need Arzela-Ascoli here

lemma A_is_seq_compact : IsSeqCompact (A F x₀ M F_bdd) := IsCompact.isSeqCompact (A_is_compact F x₀ M F_bdd)

def x_exists := ((A_is_seq_compact (x := x_c F x₀ M F_bdd) F x₀ M F_bdd) (by simp; intro n; rw [A]; aesop))
noncomputable def x_L := (x_exists F x₀ M F_bdd).choose
def x_L_spec := (x_exists F x₀ M F_bdd).choose_spec

def x_subseq_exists := (x_L_spec F x₀ M F_bdd).right
noncomputable def x_subseq := (x_subseq_exists F x₀ M F_bdd).choose
#check x_subseq F x₀ M F_bdd
def x_subseq_spec := (x_subseq_exists F x₀ M F_bdd).choose_spec

#check x_L
#check x_L_spec

-- lemma y_converges :
