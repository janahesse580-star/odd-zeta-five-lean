import OddZetaSix.B40a.Analysis.LogLookup
import OddZetaSix.SixRationalBounds

noncomputable section
namespace OddZetaSix.B40a.Cert
open Finset Real
open OddZetaSix.RationalArctanBounds

private def atanTerm (x : ℚ) (j : ℕ) :=
  (if j%2=0 then (fix:ℚ) else -fix)*x^(2*j+1)/(2*(j:ℚ)+1)

private theorem fold_terms (q : ℕ→ℚ) (xs : List ℕ) (a : Interval) :
    (xs.foldl (fun t j=>plus t ⟨qfloor (q j),qceil (q j)⟩) a) =
      ⟨a.lo+(xs.map (fun j=>qfloor (q j))).sum,a.hi+(xs.map (fun j=>qceil (q j))).sum⟩ := by
  induction xs generalizing a with
  | nil => cases a; simp
  | cons j xs ih =>
    rw [List.foldl_cons,ih]; simp only [plus,List.map_cons,List.sum_cons]; congr 1 <;> ring

private theorem atan_sum (x : ℚ) : ∑ j ∈ range 18,atanTerm x j=(fix:ℚ)*series x 18 := by
  unfold series
  rw [mul_sum]; apply sum_congr rfl; intro j _
  have sg : (if j%2=0 then (fix:ℚ) else -fix)=(fix:ℚ)*(-1:ℚ)^j := by
    rcases Nat.even_or_odd j with h|h
    · simp [Nat.even_iff.mp h,h.neg_one_pow]
    · simp [Nat.odd_iff.mp h,h.neg_one_pow]
  unfold atanTerm; rw [sg]; ring

theorem atanSmallPos_sound (x : ℚ) (hx : 0≤x) (h1 : x<1) :
    Encloses (atanSmallPos x) (Real.arctan x) := by
  have h := small_sound x 9 hx h1
  change (series x 18:ℝ)≤_ ∧ _≤(series x 19:ℝ) at h
  have hn : series x 19 = series x 18+x^37/37 := by
    unfold series; rw [show 19=18+1 by decide,sum_range_succ]; norm_num
  have ht : (0:ℝ)≤fix := by norm_num [fix]
  have hs := (Rat.castHom ℝ).congr_arg (atan_sum x)
  change ((∑ j ∈ range 18,atanTerm x j:ℚ):ℝ)=((fix:ℚ)*series x 18:ℚ) at hs
  push_cast at hs
  have rem := ceil_bound ((fix:ℚ)*x^37/37)
  push_cast at rem
  have l := sum_le_sum (s:=range 18) (fun j _=>floor_bound (atanTerm x j))
  have u := sum_le_sum (s:=range 18) (fun j _=>ceil_bound (atanTerm x j))
  change Encloses
    (let s := (List.range 18).foldl (fun t j=>plus t ⟨qfloor (atanTerm x j),qceil (atanTerm x j)⟩) ⟨0,0⟩
     ⟨s.lo,s.hi+qceil ((fix:ℚ)*x^37/37)⟩) _
  simp only [Encloses,fold_terms,zero_add,Int.cast_add]
  simp only [←List.sum_toFinset _ (List.nodup_range : (List.range 18).Nodup),List.toFinset_range]
  push_cast
  have H := mul_le_mul_of_nonneg_left h.2 ht
  rw [hn] at H; push_cast at H
  exact ⟨l.trans (hs ▸ mul_le_mul_of_nonneg_left h.1 ht),
    by linarith only [u,hs,rem,H]⟩

theorem atanSmall_sound (x : ℚ) (hl : -1<x) (hu : x<1) : Encloses (atanSmall x) (Real.arctan x) := by
  unfold atanSmall; split_ifs with h
  · have H := (atanSmallPos_sound (-x) (by linarith) (by linarith)).mul_rat (-1)
    simpa only [Rat.cast_neg,Rat.cast_one,Real.arctan_neg,neg_one_mul,neg_neg] using H
  · exact atanSmallPos_sound x (le_of_not_gt h) hu

theorem piBounds_sound : Encloses piBounds Real.pi := by
  have hl : (piBounds.lo:ℚ)≤fix*piLower := by decide +kernel
  have hu : (fix:ℚ)*piUpper≤piBounds.hi := by decide +kernel
  have hf : (0:ℝ)≤fix := by norm_num [fix]
  refine ⟨(le_trans ?_ (mul_le_mul_of_nonneg_left pi_sound.1 hf)),
    (mul_le_mul_of_nonneg_left pi_sound.2 hf).trans ?_⟩
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem atanUnit_sound (x : ℚ) (hl : 0≤x) (_hu : x≤1) : Encloses (atanUnit x) (Real.arctan x) := by
  unfold atanUnit; split_ifs with h
  · have hp : 0<x+1 := by linarith
    have low : -1<(x-1)/(x+1) := (lt_div_iff₀ hp).mpr (by linarith)
    have hi : (x-1)/(x+1)<1 := (div_lt_one hp).mpr (by linarith)
    have H := (piBounds_sound.mul_rat (1/4)).add (atanSmall_sound _ low hi)
    convert H using 1
    push_cast
    have hpR : (0:ℝ)<x+1 := by exact_mod_cast hp
    have hadd := Real.arctan_add (x:=(1:ℝ)) (y:=((x:ℝ)-1)/(x+1)) (by
      rw [one_mul,div_lt_one hpR]; linarith)
    have eqn : (1+((x:ℝ)-1)/(x+1))/(1-1*(((x:ℝ)-1)/(x+1)))=x := by field_simp <;> ring
    rw [Real.arctan_one,eqn] at hadd
    linarith
  · exact atanSmall_sound x (by linarith) (by linarith)

theorem atanBounds_sound (x : ℚ) : Encloses (atanBounds x) (Real.arctan x) := by
  let u := if x<0 then -x else x
  have hu : 0≤u := by dsimp [u]; split <;> linarith
  let v := if 1<u then plus (scale piBounds (1/2)) (scale (atanUnit (1/u)) (-1)) else atanUnit u
  have hv : Encloses v (Real.arctan u) := by
    dsimp only [v]; split_ifs with h
    · have H := (piBounds_sound.mul_rat (1/2)).add
        ((atanUnit_sound (1/u) (by positivity) ((div_le_one (by linarith)).mpr h.le)).mul_rat (-1))
      convert H using 1
      push_cast
      simp only [one_div]
      rw [Real.arctan_inv_of_pos (show (0:ℝ)<u by exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<1) h))]
      ring
    · exact atanUnit_sound u hu (le_of_not_gt h)
  change Encloses (if x<0 then scale v (-1) else v) _
  split_ifs with h
  · simpa [u,h] using hv.mul_rat (-1)
  · simpa [u,h] using hv

end OddZetaSix.B40a.Cert
