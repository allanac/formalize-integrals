import Mathlib.Topology.MetricSpace.Equicontinuity

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
variable (F : E →ᵇ E)
variable (x₀ : E)
#where

-- variable (M : NNReal)
-- variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

noncomputable def y_c (k : ℕ) : (Set.Icc 0 (1 : ℝ)) → E
| t => y F x₀ (1/((k : ℝ)+1)) t

noncomputable def x_c' (k : ℕ) : (Set.Icc 0 (1 : ℝ)) → E
| t => x F x₀ (1/((k : ℝ)+1)) t
open ENNReal
lemma x_is_lipschitz : ∀ (k : ℕ), LipschitzWith (M F) (x_c' F x₀ k) := by
  intro k
  rw [lipschitzWith_iff_dist_le_mul]
  intro z1 z2
  have : M F * dist z1 z2 = M F * norm ((z1:ℝ)-(z2:ℝ)) := by
    rw [mul_eq_mul_left_iff]
    left
    rfl
  simp
  rw [this]
  rw [x_c',x_c']
  simp
  have := Claim1 F x₀ (1/((k : ℝ)+1)) (one_div_pos.mpr (Nat.cast_add_one_pos _)) z1 z2
  simp at *
  rw [dist_eq_norm]
  apply this
  · rcases z2 with ⟨z2', z2h⟩
    apply (Set.mem_Icc.mp z2h).left
  · rcases z1 with ⟨z1', z1h⟩
    apply (Set.mem_Icc.mp z1h).left

#check x_is_lipschitz F x₀
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
  continuous_toFun := LipschitzWith.continuous (x_is_lipschitz F x₀ k)


#check x_c F x₀

#check x

open Filter Topology

lemma equicontinuous_of_lipschitzWith [PseudoMetricSpace α] [PseudoMetricSpace β] {f : ι → α → β} {K}
    (h : ∀ i, LipschitzWith K (f i)) : Equicontinuous f := by
  apply Metric.equicontinuous_of_continuity_modulus fun x ↦ K*x
  convert tendsto_id.const_mul (K : ℝ) ; simp
  simp [lipschitzWith_iff_dist_le_mul] at h
  tauto

lemma x_c_lip : ∀ (k : ℕ), LipschitzWith (M F) (x_c F x₀ k) := x_is_lipschitz F x₀

lemma x_c_eq_cont : Equicontinuous (fun n ↦ (x_c F x₀ n)) :=
  equicontinuous_of_lipschitzWith (x_c_lip F x₀)

def A := Set.range (x_c F x₀)


#check A

lemma A_is_compact : IsCompact (A F x₀) := by sorry
-- need Arzela-Ascoli here

lemma A_is_seq_compact : IsSeqCompact (A F x₀) := IsCompact.isSeqCompact (A_is_compact F x₀)

def x_exists := ((A_is_seq_compact (x := x_c F x₀) F x₀) (by simp; intro n; rw [A]; aesop))
noncomputable def x_L := (x_exists F x₀).choose
def x_L_spec :  (x_L F x₀) ∈ A F x₀ ∧ ∃ φ : ℕ → ℕ , StrictMono φ ∧ Tendsto (x_c F x₀ ∘ φ) atTop (𝓝 (x_L F x₀))
  := (x_exists F x₀).choose_spec

def x_subseq_exists := (x_L_spec F x₀).right
noncomputable def x_subseq := (x_subseq_exists F x₀).choose
#check x_subseq F x₀
def x_subseq_spec : StrictMono (x_subseq F x₀) ∧ Tendsto (x_c F x₀ ∘ (x_subseq F x₀)) atTop (𝓝 (x_L F x₀))
  := (x_subseq_exists F x₀).choose_spec

#check x_L F x₀
#check x_subseq F x₀
#check x_L_spec F x₀
#check x_subseq_spec F x₀
#check y_c F x₀
#check fun (z:ℕ) => (y_c F x₀ (x_subseq F x₀ z))

open Filter
#check nhds
#check Tendsto (fun z => (y F x₀ (x_subseq F x₀ z ))) atTop

lemma x_converges : TendstoUniformly (fun z => (x_c F x₀ (x_subseq F x₀ z)).toFun) (x_L F x₀) atTop :=
  BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (x_subseq_spec F x₀).right

lemma y_converges' : TendstoUniformly (fun z => (y_c F x₀ (x_subseq F x₀ z)) - (x_c F x₀ (x_subseq F x₀ z)).toFun) 0 atTop := by
  rw [Metric.tendstoUniformly_iff]
  let F_bdd := M F + 1
  have F_bdd_pos : 0 < F_bdd := by apply lt_add_of_le_of_pos (norm_nonneg _); norm_num
  intro ε epos
  simp only [eventually_atTop]
  simp only [ContinuousMap.toFun_eq_coe,x_c]--,ContinuousMap.mk_coe,x_c,x_c',y_c]
  simp
  simp [y_c,x_c',x,y]
  use Nat.ceil (F_bdd/ε)
  intro b hb a ann _
  rw [norm_smul]
  have : ε = ε/F_bdd*F_bdd := by
    rw [div_mul_cancel]
    have := (ne_of_lt F_bdd_pos).symm
    norm_cast
  rw [this]
  apply _root_.mul_lt_mul'
  swap
  apply lt_add_of_le_of_pos (BoundedContinuousFunction.norm_coe_le_norm F _)
  norm_num
  swap
  apply norm_nonneg
  swap
  apply div_pos epos F_bdd_pos
  rw [lam,div_inv_eq_mul,N,div_inv_eq_mul,norm_mul]
  norm_num
  let z := a * ((x_subseq F x₀ b) + 1)
  have znn : 0 ≤ z := by
    apply mul_nonneg ann
    apply le_of_lt (Nat.cast_add_one_pos _)
  rw [Nat.cast_floor_eq_cast_int_floor znn]
  rw [Int.self_sub_floor,Int.abs_fract]
  have zle1: Int.fract (a * (↑(x_subseq F x₀ b) + 1)) ≤ 1 := le_of_lt (Int.fract_lt_one _)
  have : ε / (↑(M F) + 1) = 1 * (ε / (↑(M F) + 1)) := by rw[one_mul]
  rw [this]
  apply mul_le_mul zle1 _ (inv_nonneg.mpr (abs_nonneg _)) (le_of_lt one_pos)
  have z' : 0 ≤ (((x_subseq F x₀ b) + 1) : ℝ)⁻¹ := by
    apply inv_nonneg.mpr
    apply le_of_lt (Nat.cast_add_one_pos _)
  rw [← abs_inv]
  rw [abs_of_nonneg z']
  rw [inv_le,inv_div]
  apply le_add_of_le_of_nonneg _ (le_of_lt one_pos)
  have : (b: ℝ) ≤ ↑(x_subseq F x₀ b) := by
    norm_cast
    apply StrictMono.id_le
    apply (x_subseq_spec F x₀).left
  apply le_trans _ this
  have hb' : ⌈↑F_bdd / ε⌉₊ ≤ (b : ℝ) := by norm_cast
  apply le_trans _ hb'
  apply Nat.le_ceil
  apply Nat.cast_add_one_pos
  apply div_pos epos (lt_add_of_le_of_pos (norm_nonneg _) one_pos)

set_option maxHeartbeats 0
lemma y_converges : TendstoUniformly (fun z => (y_c F x₀ (x_subseq F x₀ z))) (x_L F x₀).toFun atTop := by
  have test : TendstoUniformly (fun z => (y_c F x₀ (x_subseq F x₀ z))) (x_L F x₀).toFun atTop =
    TendstoUniformly (fun z => (y_c F x₀ (x_subseq F x₀ z ) - (x_c F x₀ (x_subseq F x₀ z)).toFun + (x_c F x₀ (x_subseq F x₀ z)).toFun)) (0 + (x_L F x₀).toFun) atTop := by simp
  rw [test]
  apply TendstoUniformly.add
  apply y_converges' F x₀
  apply x_converges F x₀
