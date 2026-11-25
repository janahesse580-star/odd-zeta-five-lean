import OddZetaSix.B40a.Arithmetic.MiddleIntegral
import OddZetaSix.B40a.Arithmetic.WeightedPNT
import OddZetaSix.B40a.Certificate.ArithmeticNativeAudit

noncomputable section
namespace OddZetaSix.B40a
open Finset Filter MeasureTheory Set Cert Cert.Transport
open scoped Topology
set_option maxRecDepth 32768
attribute [local irreducible] middleRows

abbrev MiddleIndex := Fin middleRows.length
def midRow (i : MiddleIndex) := middleRows.get i
theorem midRow_mem (i : MiddleIndex) : midRow i ∈ middleRows := List.get_mem _ _
def midLo (i : MiddleIndex) : ℝ := (midRow i).left
def midHi (i : MiddleIndex) : ℝ := (midRow i).right
def midW (i : MiddleIndex) := (model _ (midRow_mem i)).eval

private theorem ends_ok : middleRows.all (fun r=>decide (r.right≤50))=true := by
  unfold middleRows
  decide +kernel

private theorem end_bounds (i : MiddleIndex) : 0<midLo i ∧ midLo i≤midHi i ∧ midHi i≤84 := by
  have H := row_sides (midRow_mem i)
  have E := of_decide_eq_true (List.all_eq_true.mp ends_ok _ (midRow_mem i))
  unfold midLo midHi
  exact ⟨by exact_mod_cast H.1,by exact_mod_cast H.2.le,by
    exact_mod_cast (E.trans (by norm_num : (50:ℚ)≤84))⟩

private theorem chain_find {xs : List ArithRow} {a b : ℚ} {t : ℝ}
    (hc : arithChain a b xs=true) (ht : (a:ℝ)<t ∧ t≤b) :
    ∃ r ∈ xs,(r.left:ℝ)<t ∧ t≤r.right := by
  induction xs generalizing a with
  | nil => simp only [arithChain,decide_eq_true_eq] at hc; subst a; linarith [ht.1,ht.2]
  | cons r xs ih =>
    simp only [arithChain,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases h : t≤(r.right:ℝ)
    · exact ⟨r,List.mem_cons_self,hc.1 ▸ ht.1,h⟩
    · obtain ⟨u,hu,hk⟩ := ih hc.2 ⟨lt_of_not_ge h,ht.2⟩
      exact ⟨u,List.mem_cons_of_mem _ hu,hk⟩

def midExceptional (n : ℕ) : Finset ℕ :=
  (insert n (univ.image (fun i : MiddleIndex=>⌊midHi i*(n:ℝ)⌋₊))) ∩ cutoffPrimes n

private theorem budget : (∑ i : MiddleIndex,∫ x in midLo i..midHi i,midW i x)/2000 ≤
    (5244756877432/1000000000000 : ℝ) := by
  have hs := sum_le_sum (s:=(univ:Finset MiddleIndex)) (fun i _=>model_integral (midRow_mem i))
  have hv : (∑ i : MiddleIndex,rowValue false (midRow i)) = (middleRows.map (rowValue false)).sum := by
    rw [←List.sum_ofFn]
    exact List.ofFn_getElem_eq_map middleRows (rowValue false) |> congrArg List.sum
  have hb := checkedArithRows_sum_bound false _ Native.middle_rows_checked
  rw [←hv,middleRows_exact_budget] at hb
  have hR := (Rat.cast_le (K:=ℝ)).mpr hb
  rw [Rat.cast_sum] at hR
  rw [←Finset.mul_sum] at hs
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2000)).mpr
  apply hs.trans
  norm_num [bigUnit] at hR
  linarith only [hR]

theorem middle_prime_cost_rate (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,bandPrimeCost n (11/20) 50 / normalizer n ≤
      5244756877432/1000000000000+δ := by
  have H := bandPrimeCost_rate_of_piecewise_majorant (univ:Finset MiddleIndex) (11/20) 50
    (by norm_num) (by norm_num) midLo midHi midW
    (fun i _=>(end_bounds i).1) (fun i _=>(end_bounds i).2.1) (fun i _=>(end_bounds i).2.2)
    (fun i _=>(model _ _).eval_continuous.continuousOn) (fun i _=>model_nonneg (midRow_mem i))
    123648 (by norm_num) midExceptional ((univ:Finset MiddleIndex).card+1)
    (fun _=>inter_subset_right) (Eventually.of_forall fun n=> by
      apply (Finset.card_le_card Finset.inter_subset_left).trans
      exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1))
    (by
      filter_upwards [eventually_gt_atTop (400:ℕ)] with n hn
      have hnR : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
      intro p hp hexc
      have hmem := Finset.mem_filter.mp hp
      obtain ⟨hu,hp'⟩ := Nat.mem_primesLE.mp hmem.1
      have hlow := hmem.2
      have hup : (p:ℝ)≤50*(n:ℝ) := (Nat.le_floor_iff (by positivity)).mp hu
      have inCut : p∈cutoffPrimes n := Nat.mem_primesLE.mpr ⟨by exact_mod_cast (show (p:ℝ)≤84*n by linarith),hp'⟩
      have neq : p≠n := by intro he; apply hexc; exact mem_inter.mpr ⟨mem_insert.mpr (Or.inl he),inCut⟩
      have l : (11/20:ℝ) < (p:ℝ)/n := (lt_div_iff₀ hnR).mpr hlow
      have u : (p:ℝ)/n ≤ 50 := (div_le_iff₀ hnR).mpr hup
      obtain ⟨r,hr,hl,hh⟩ := chain_find middle_chain (t:=(p:ℝ)/n) (by push_cast; exact ⟨l,u⟩)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
      change midRow i=r at hi
      subst r
      have hl' : midLo i*n < p := (lt_div_iff₀ hnR).mp hl
      have hh' : (p:ℝ) ≤ midHi i*n := (div_le_iff₀ hnR).mp hh
      have strong : (p:ℝ)/n < midHi i := by
        apply lt_of_le_of_ne hh
        intro he
        have eq : midHi i*(n:ℝ)=p := ((div_eq_iff hnR.ne').mp he).symm
        apply hexc
        exact mem_inter.mpr ⟨mem_insert.mpr (Or.inr (mem_image.mpr ⟨i,mem_univ _,by rw [eq,Nat.floor_natCast]⟩)),inCut⟩
      have band : 11*n≤20*p := by exact_mod_cast (show (11:ℝ)*n≤20*p by linarith)
      have hnlt : n<2*p := by omega
      have hpl : 168<p := by omega
      have sq : 84*n<p^2 := by nlinarith only [Nat.mul_lt_mul_of_pos_left hnlt (by decide : 0<84),
          Nat.mul_lt_mul_of_pos_right hpl hp'.pos]
      letI : Fact p.Prime := ⟨hp'⟩
      have hdisc := MiddleGrid.primeExponent_le_middleValue n p (by omega) (by omega) sq band neq
      have eq := model_at (midRow_mem i) ((p:ℚ)/n) (by
        push_cast; exact ⟨hl,strong⟩)
      push_cast at eq
      refine ⟨i,mem_univ _,hl',hh',?_⟩
      change _≤(n:ℝ)*(model _ _).eval ((p:ℝ)/n)+123648
      rw [eq]
      convert hdisc using 1 <;> ring)
    δ hδ
  filter_upwards [H] with n h
  linarith only [h,budget]
end OddZetaSix.B40a
