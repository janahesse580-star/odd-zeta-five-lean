import OddZetaSix.B40a.Arithmetic.CertificateRows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Real interval semantics for the fixed-point logarithm core. -/
noncomputable section
namespace OddZetaSix.B40a.Cert
open Finset Set MeasureTheory
open scoped BigOperators _root_.Interval

theorem half_log_sharp_remainder {x : ℝ} (hx : 0≤x) (h1 : x<1) :
    1/2*Real.log ((1+x)/(1-x)) - (∑ j ∈ range 18, x^(2*j+1)/(2*(j : ℝ)+1))
      ≤ x^37/(37*(1-x^2)) := by
  let f (t : ℝ) := 1/2*Real.log ((1+t)/(1-t)) - (∑ j ∈ range 18, t^(2*j+1)/(2*(j : ℝ)+1))
  let d (t : ℝ) := t^36/(1-t^2)
  have hnon (t : ℝ) (ht : t ∈ uIcc 0 x) : 0<1-t^2 := by
    rw [uIcc_of_le hx] at ht
    nlinarith [mul_pos (show 0 < 1-t by linarith [ht.2]) (show 0<1+t by linarith [ht.1])]
  have hd (t : ℝ) (ht : t ∈ uIcc 0 x) : HasDerivAt f (d t) t := by
    rw [uIcc_of_le hx] at ht
    simpa only [f,d,← pow_mul,Nat.reduceMul,Nat.cast_succ,Nat.cast_mul,Nat.cast_ofNat] using
      Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range 18
        (show -1<t by linarith [ht.1]) (ht.2.trans_lt h1)
  have hi : IntervalIntegrable d volume 0 x :=
    (continuousOn_id.pow 36 |>.div (continuousOn_const.sub (continuousOn_id.pow 2))
      (fun t ht => (hnon t ht).ne')).intervalIntegrable
  have hj : IntervalIntegrable (fun t : ℝ => t^36/(1-x^2)) volume 0 x :=
    (show Continuous (fun t : ℝ => t^36/(1-x^2)) by fun_prop).intervalIntegrable _ _
  have hb : (∫ t in 0..x, d t) ≤ ∫ t in 0..x, t^36/(1-x^2) := by
    apply intervalIntegral.integral_mono_on hx hi hj
    intro t ht
    have h2 := pow_le_pow_left₀ ht.1 ht.2 2
    exact div_le_div_of_nonneg_left (pow_nonneg ht.1 _) (hnon x right_mem_uIcc) (by linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    intervalIntegral.integral_div,integral_pow] at hb
  have hf0 : f 0=0 := by norm_num [f]
  rw [hf0,sub_zero] at hb
  norm_num [f,div_div] at hb ⊢
  exact hb

private theorem foldl_atanh_sum (z : ℚ) (is : List ℕ) (acc : Interval) :
    (is.foldl (fun (t : Interval) (j : ℕ) =>
      let term := 2*fix*z^(2*j+1)/(2*(j : ℚ)+1)
      plus t ⟨qfloor term,qceil term⟩) acc) =
      ⟨acc.lo+(is.map fun (j : ℕ) => qfloor (2*fix*z^(2*j+1)/(2*(j : ℚ)+1))).sum,
        acc.hi+(is.map fun (j : ℕ) => qceil (2*fix*z^(2*j+1)/(2*(j : ℚ)+1))).sum⟩ := by
  induction is generalizing acc with
  | nil => cases acc; simp
  | cons j is ih =>
    rw [List.foldl_cons,ih]
    simp only [plus,List.map_cons,List.sum_cons]
    congr 1 <;> ring

private theorem floor_le_real (q : ℚ) : (qfloor q : ℝ) ≤ (q : ℝ) := by
  rw [qfloor_eq_floor,← Rat.floor_cast (α := ℝ)]
  exact Int.floor_le _

private theorem real_le_ceil (q : ℚ) : (q : ℝ) ≤ (qceil q : ℝ) := by
  rw [qceil_eq_ceil,← Rat.ceil_cast (α := ℝ)]
  exact Int.le_ceil _

/-- The exact 18-term checker, including its one-sided remainder. -/
theorem atanhLog_sound (x : ℚ) (hx : 1≤x) :
    ((atanhLog x).lo : ℝ) ≤ (fix : ℝ)*Real.log (x : ℝ) ∧
      (fix : ℝ)*Real.log (x : ℝ) ≤ ((atanhLog x).hi : ℝ) := by
  let z : ℚ := (x-1)/(x+1)
  let r : ℝ := (z : ℝ)
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hre : r = ((x : ℝ)-1)/((x : ℝ)+1) := by unfold r z; push_cast; rfl
  have hr0 : 0≤r := by rw [hre]; exact div_nonneg (by linarith) (by linarith)
  have hr1 : r<1 := by
    rw [hre,div_lt_one (by linarith : (0:ℝ)<(x : ℝ)+1)]
    linarith
  have hratio : (1+r)/(1-r) = (x : ℝ) := by
    rw [hre]
    have hpos : (x : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hr0 hr1 18
  have hu := half_log_sharp_remainder hr0 hr1
  rw [hratio] at hl hu
  let term := fun j : ℕ => 2*fix*z^(2*j+1)/(2*(j : ℚ)+1)
  let rem : ℚ := 2*fix*z^37/(37*(1-z*z))
  have ht (j : ℕ) : (term j : ℝ) = 2*(fix : ℝ)*(r^(2*j+1)/(2*(j : ℝ)+1)) := by
    unfold term r
    push_cast
    ring
  have hrem : (rem : ℝ) = 2*(fix : ℝ)*(r^37/(37*(1-r^2))) := by
    unfold rem r
    push_cast
    ring
  have hF : (0:ℝ) ≤ fix := by norm_num [fix]
  have hL := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(fix : ℝ) by positivity)
  have hU := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2*(fix : ℝ) by positivity)
  have htermSum :
      (∑ j ∈ range 18, (term j : ℝ)) =
        2*(fix : ℝ)*(∑ j ∈ range 18, r^(2*j+1)/(2*(j : ℝ)+1)) := by
    simp only [ht,Finset.mul_sum]
  have lo := sum_le_sum (s := range 18) (fun j _ => floor_le_real (term j))
  have hi := sum_le_sum (s := range 18) (fun j _ => real_le_ceil (term j))
  dsimp only [atanhLog]
  rw [foldl_atanh_sum]
  simp only [zero_add,Int.cast_add]
  simp only [← List.sum_toFinset _ (List.nodup_range : (List.range 18).Nodup), List.toFinset_range]
  push_cast
  constructor
  · calc
      _ ≤ ∑ j ∈ range 18, (term j : ℝ) := lo
      _ ≤ _ := by rw [htermSum]; linarith only [hL]
  · calc
      _ ≤ (∑ j ∈ range 18, (term j : ℝ))+(rem : ℝ) := by
        rw [htermSum,hrem]
        linarith only [hU]
      _ ≤ _ := add_le_add hi (real_le_ceil rem)

end OddZetaSix.B40a.Cert
