import OddZetaSix.B40a.Analysis.EdgeCoordinates
import OddZetaSix.B40a.Analysis.WeightedContour
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Cert.Chord Set Real MeasureTheory Filter Finset
open scoped Interval

def lengthWeight (n : ℕ) (q : ℝ) (a : BendParam) :=
  ‖edgeDelta n q a.1‖*Real.exp (-edgeY n q a.1.2 a.2)

private theorem delta_bound (n : ℕ) (hn : 0<n) (q : ℝ) (e : BendEdge) :
    ‖edgeDelta n q e‖ ≤ scaleN n*(|stopX e.2-nodeX e.2|+|stopY n q e.2-bendHeight e.2|) := by
  obtain ⟨A,B⟩ := scaled_node n hn e.1 e.2
  obtain ⟨C,E⟩ := scaled_stop n hn q e
  let d := edgeDelta n q e
  have r : d.re=scaleN n*(stopX e.2-nodeX e.2) := by
    change (edgeStop n q e).re-(bendNode n e.1 e.2).re=_
    linear_combination C-A
  have i : d.im=contourSide e.1*(scaleN n*(stopY n q e.2-bendHeight e.2)) := by
    change (edgeStop n q e).im-(bendNode n e.1 e.2).im=_
    linear_combination E-B
  have D : 0≤scaleN n := by unfold scaleN; positivity
  apply (Complex.norm_le_abs_re_add_abs_im d).trans_eq
  rw [r,i,abs_mul,abs_mul,abs_mul,abs_of_nonneg D]
  rcases e with ⟨s,k⟩; cases s <;> simp [contourSide] <;> ring

private theorem integrate_profile (a b : ℝ) :
    ∫ t : ℝ in (0:ℝ)..1, (b-a)*Real.exp (-lerp t a b)=Real.exp (-a)-Real.exp (-b) := by
  have E : (fun t=>lerp t a b)=(fun t=>a+(b-a)*t) := by funext t; unfold lerp; ring
  have der (t : ℝ) : HasDerivAt (fun t=> -Real.exp (-lerp t a b))
      ((b-a)*Real.exp (-lerp t a b)) t := by
    have L : HasDerivAt (fun t=>lerp t a b) (b-a) t := by
      rw [E]; apply (((hasDerivAt_id t).const_mul (b-a)).const_add a).congr_deriv; ring
    apply ((L.neg.exp).neg).congr_deriv; simp only [Pi.neg_apply]; ring
  have I : IntervalIntegrable (fun t=> (b-a)*Real.exp (-lerp t a b)) volume 0 1 := by
    apply Continuous.intervalIntegrable; unfold lerp; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>der t) I]
  simp [lerp]; ring

theorem length_row (n : ℕ) (hn : 0<n) (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge) :
    ∫ t : ℝ in Ioc 0 1, lengthWeight n q (e,t) ≤ 2*scaleN n := by
  let j := e.2
  let a := bendHeight j
  let b := stopY n q j
  let D := scaleN n
  have hD : 0≤D := by unfold D scaleN; positivity
  have hb : a≤b := (edgeY_range n hn q hq j (t:=0) ⟨le_rfl,by norm_num⟩).1.trans
    (edgeY_range n hn q hq j (t:=0) ⟨le_rfl,by norm_num⟩).2
  have h0 := (nodeY_bounds j).1
  have hd := delta_bound n hn q e
  have cont : Continuous (fun t=>lengthWeight n q (e,t)) := by
    unfold lengthWeight edgeY lerp; fun_prop
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  by_cases h : j.val<7
  · have xrange : |stopX j-nodeX j|≤1 := by
      have A := nodeX_bounds j; have S := nodeX_bounds (nextNode j h)
      simp only [stopX,dite_eq_left h]
      apply abs_le.mpr; constructor <;> linarith only [A.1,A.2,S.1,S.2]
    have ydiff : |b-a|≤1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hb)]
      have B : b≤1 := by simpa [b,stopY,h] using (nodeY_bounds (nextNode j h)).2
      linarith only [B,h0]
    have hd' : ‖edgeDelta n q e‖≤2*D := hd.trans (by
      change D*(|stopX j-nodeX j|+|b-a|)≤_; nlinarith only [mul_le_mul_of_nonneg_left (add_le_add xrange ydiff) hD])
    calc _ ≤ ∫ t : ℝ in (0:ℝ)..1, 2*D := by
           apply intervalIntegral.integral_mono_on (by norm_num) (cont.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
           intro t ht
           have pos := h0.trans (edgeY_range n hn q hq j ht).1
           exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr pos))).trans hd'
         _ = _ := by simp [D]
  · have jj : j=7 := Fin.ext (by have := j.isLt; change j.val=7; omega)
    have hx : stopX j=nodeX j := by rw [jj]; rfl
    have dd : ‖edgeDelta n q e‖≤D*(b-a) := by
      change _≤D*(|stopX j-nodeX j|+|b-a|) at hd
      simpa [hx,abs_of_nonneg (sub_nonneg.mpr hb)] using hd
    have I : Continuous (fun t=>D*((b-a)*Real.exp (-lerp t a b))) := by unfold lerp; fun_prop
    calc _ ≤ ∫ t : ℝ in (0:ℝ)..1, D*((b-a)*Real.exp (-lerp t a b)) := by
           apply intervalIntegral.integral_mono_on (by norm_num) (cont.intervalIntegrable 0 1) (I.intervalIntegrable 0 1)
           intro t _
           simpa only [lengthWeight,edgeY,mul_assoc] using mul_le_mul_of_nonneg_right dd (Real.exp_pos (-lerp t a b)).le
         _ = D*(Real.exp (-a)-Real.exp (-b)) := by rw [intervalIntegral.integral_const_mul,integrate_profile]
         _ ≤ _ := by
           have hA : Real.exp (-a)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr h0)
           have W := mul_le_mul_of_nonneg_left (show Real.exp (-a)-Real.exp (-b)≤1 by linarith only [hA,Real.exp_pos (-b)]) hD
           linarith only [W,hD]

end OddZetaSix.B40a.Witness
