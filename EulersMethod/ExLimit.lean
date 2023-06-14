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
variable {E: Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : E → E)
variable (x₀ : E)
#where

variable (M : ℝ) (M_nn : 0 ≤ M)
variable (F_bdd : ∀ e : E, ‖F e‖ ≤ M)

noncomputable def x_c' (k : ℕ) : (Set.Icc 0 (1 : ℝ)) → E
| t => x F x₀ (1/((k : ℝ)+1)) (t)

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
 continuous_toFun := by sorry


#check x_c

#check x

lemma x_c_eq_cont_at {a : ℝ} (_ : a ∈ Set.Icc 0 1) : EquicontinuousAt (x_c F x₀) a := by sorry
-- use Claim1 here

lemma x_c_eq_cont : Equicontinuous (x_c F x₀) := by sorry
-- use previous lemma

-- has to be redefined: structures
def A := Set.range (x_c F x₀) 


#check A

lemma A_is_compact : IsCompact (A F x₀) := by sorry
-- need Arzela-Ascoli here

lemma A_is_seq_compact : IsSeqCompact (A F x₀) := IsCompact.isSeqCompact (A_is_compact F x₀)

def x_exists := ((A_is_seq_compact (x := x_c F x₀) F x₀) (by simp; intro n; rw [A]; aesop))
noncomputable def x_L := (x_exists F x₀).choose
def x_L_spec := (x_exists F x₀).choose_spec

def x_subseq_exists := (x_L_spec F x₀).right
noncomputable def x_subseq := (x_subseq_exists F x₀).choose
#check x_subseq F x₀
def x_subseq_spec := (x_subseq_exists F x₀).choose_spec

#check x_L
#check x_L_spec

-- lemma y_converges : 
