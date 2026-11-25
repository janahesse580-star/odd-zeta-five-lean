import OddZetaSix.B40a.Analysis.ContourMoment

/-! Uniform fourth-cotangent-derivative bound on both finite bent contours,
including the half-integer crossing. The norm identity and cosine estimate
adapt the MIT-licensed SixContour module in this repository. -/
noncomputable section
namespace OddZetaSix.B40a
open Complex Set
private theorem sin_norm_sq (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hre : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  have him : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have hh := Real.cosh_sq w.im
  have ht := Real.sin_sq_add_cos_sq w.re
  linear_combination Real.sin w.re ^ 2 * hh + Real.sinh w.im ^ 2 * ht


private def sineFactor : ℝ :=
  min ((1/2)*Real.exp (-(Real.pi/8))) ((1-Real.exp (-(Real.pi/4)))/2)
private theorem sineFactor_pos : 0<sineFactor := by
  unfold sineFactor
  exact lt_min (by positivity) (div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))) (by norm_num))

private theorem sine_min (n : ℕ) (z : ℂ) (hc : |z.re-contourAbscissa n|≤2*|z.im|) :
    sineFactor*Real.exp (Real.pi*|z.im|)≤‖Complex.sin ((Real.pi:ℂ)*z)‖ := by
  let w := (Real.pi:ℂ)*z
  let t := Real.pi*|z.im|
  have him : w.im=Real.pi*z.im := by simp [w]
  have hre : w.re=Real.pi*z.re := by simp [w]
  have ab : |w.im|=t := by rw [him,abs_mul,abs_of_pos Real.pi_pos]
  have S := sin_norm_sq w
  change _ ≤ ‖Complex.sin w‖
  by_cases hy : |z.im|≤1/8
  · let a := Real.pi*(z.re-contourAbscissa n)
    have lh : |a|≤Real.pi/3 := by
      unfold a; rw [abs_mul,abs_of_pos Real.pi_pos]
      nlinarith only [mul_le_mul_of_nonneg_left (hc.trans (show 2*|z.im|≤1/4 by linarith only [hy])) Real.pi_pos.le,
        Real.pi_pos]
    have H := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (show Real.pi/3≤Real.pi by linarith [Real.pi_pos]) lh
    rw [Real.cos_abs,Real.cos_pi_div_three] at H
    have E : w.re=(a+Real.pi/2)+((-(anchor n:ℤ)-1:ℤ):ℝ)*Real.pi := by
      rw [hre]; unfold a contourAbscissa; push_cast; ring
    have W : |Real.sin w.re|=|Real.cos a| := by
      rw [E,Real.sin_add_int_mul_pi,Real.sin_add_pi_div_two,abs_mul,abs_neg_one_zpow,one_mul]
    have hs : |Real.sin w.re|≤‖Complex.sin w‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _); rw [sq_abs,S]; linarith only [sq_nonneg (Real.sinh w.im)]
    have low : 1/2≤‖Complex.sin w‖ := H.trans ((le_abs_self _).trans (W ▸ hs))
    have ht : t≤Real.pi/8 := by unfold t; nlinarith only [mul_le_mul_of_nonneg_left hy Real.pi_pos.le]
    have ex := Real.exp_le_exp.mpr (show -(Real.pi/8)+t≤0 by linarith)
    rw [Real.exp_add,Real.exp_zero] at ex
    apply (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos t).le).trans
    change 1/2*Real.exp (-(Real.pi/8))*Real.exp t≤_
    linarith only [ex,low]
  · have ht : Real.pi/8≤t := by unfold t; nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hy) Real.pi_pos.le]
    have low : |Real.sinh w.im|≤‖Complex.sin w‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _); rw [sq_abs,S]; linarith only [sq_nonneg (Real.sin w.re)]
    rw [Real.abs_sinh,ab,Real.sinh_eq] at low
    have e := Real.exp_le_exp.mpr (show -t≤ -(Real.pi/4)+t by linarith)
    rw [Real.exp_add] at e
    apply (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos t).le).trans
    change (1-Real.exp (-(Real.pi/4)))/2*Real.exp t ≤_
    linarith only [low,e]

def bentTrigConstant := Real.pi^5/sineFactor^5

theorem bentTrigConstant_positive : 0<bentTrigConstant :=
  div_pos (pow_pos Real.pi_pos _) (pow_pos sineFactor_pos _)

theorem bent_trig_decay (n : ℕ) (z : ℂ) (hc : |z.re-contourAbscissa n|≤2*|z.im|) :
    ‖sixContourKernel z‖ ≤ bentTrigConstant*Real.exp (-2*Real.pi*|z.im|) := by
  let w := (Real.pi:ℂ)*z
  have him : w.im=Real.pi*z.im := by simp [w]
  have hcos_le : ‖Complex.cos w‖ ≤ Real.exp (Real.pi * |z.im|) := by
    rw [Complex.cos, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
    simp only [Complex.norm_exp, mul_re, I_re, I_im, mul_zero, mul_one,
      zero_sub, neg_im, neg_neg, him] at h
    have h1 := Real.exp_le_exp.mpr (show Real.pi * z.im ≤ Real.pi * |z.im| by
      exact mul_le_mul_of_nonneg_left (le_abs_self z.im) Real.pi_pos.le)
    have h2 := Real.exp_le_exp.mpr (show -(Real.pi * z.im) ≤ Real.pi * |z.im| by
      have := neg_le_abs z.im; nlinarith [Real.pi_pos])
    linarith
  have hnum : ‖Complex.cos w ^ 3 + 2 * Complex.cos w‖ ≤ 3 * Real.exp (Real.pi * |z.im|) ^ 3 := by
    have htri := norm_add_le (Complex.cos w ^ 3) (2 * Complex.cos w)
    rw [Complex.norm_pow, norm_mul] at htri; norm_num only [Complex.norm_ofNat] at htri
    have he1 : 1 ≤ Real.exp (Real.pi * |z.im|) := Real.one_le_exp (by positivity)
    have h13 : Real.exp (Real.pi * |z.im|) ≤ Real.exp (Real.pi * |z.im|) ^ 3 := by
      simpa using pow_le_pow_right₀ he1 (show 1 ≤ 3 by omega)
    have hc3 : ‖Complex.cos w‖ ^ 3 ≤ Real.exp (Real.pi * |z.im|) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hcos_le 3
    linarith

  have hs := sine_min n z hc
  have hspos : 0<‖Complex.sin w‖ := (mul_pos sineFactor_pos (Real.exp_pos _)).trans_le hs
  rw [sixContourKernel_eq _ (norm_pos_iff.mp hspos),norm_div,norm_mul,norm_pow]
  change ‖(Real.pi:ℂ)‖^5 * ‖Complex.cos w^3+2*Complex.cos w‖ / ‖3*Complex.sin w^5‖ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_mul,norm_pow]
  norm_num only [Complex.norm_ofNat]
  rw [div_le_iff₀ (by positivity)]
  have hden := pow_le_pow_left₀ (mul_pos sineFactor_pos (Real.exp_pos _)).le hs 5
  have he : Real.exp (-2*Real.pi*|z.im|)*Real.exp (Real.pi*|z.im|)^5=Real.exp (Real.pi*|z.im|)^3 := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]; congr 1; ring
  have pos : 0≤bentTrigConstant*Real.exp (-2*Real.pi*|z.im|) := mul_nonneg (div_nonneg (by positivity)
    (pow_pos sineFactor_pos _).le) (Real.exp_pos _).le
  apply (mul_le_mul_of_nonneg_left hnum (by positivity : 0≤Real.pi^5)).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ)≤3)) pos)
  unfold bentTrigConstant
  rw [mul_pow,←he]
  field_simp [sineFactor_pos.ne'] <;> norm_num

private theorem node_cone (n : ℕ) (s : Bool) (k : Fin 8) :
    |(bendNode n s k).re-contourAbscissa n| ≤ 2*(contourSide s*(bendNode n s k).im) := by
  cases s <;> simpa [bendNode,contourSide] using bendNode_offset_le n k

theorem edge_cone (n : ℕ) (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge)
    {t : ℝ} (ht : t∈Icc 0 1) :
    |(edgePoint n q (e,t)).re-contourAbscissa n| ≤ 2*|(edgePoint n q (e,t)).im| := by
  let a := edgeStart n e
  let b := edgeStop n q e
  have A : |a.re-contourAbscissa n|≤2*(contourSide e.1*a.im) := node_cone n e.1 e.2
  have B : |b.re-contourAbscissa n|≤2*(contourSide e.1*b.im) := by
    dsimp only [b,edgeStop]
    split_ifs
    · exact node_cone n e.1 _
    · have H := (bendNode_offset_le n 7).trans (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2))
      rcases e with ⟨s,k⟩; cases s <;> simpa [contourSide] using H
  have he : edgePoint n q (e,t)=(1-t) • a+t • b := by
    unfold edgePoint edgeDelta; simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
    change a+(t:ℂ)*(b-a)=(1-t)*a+t*b; ring
  rw [he]
  simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  have off : (1-t)*a.re+t*b.re-contourAbscissa n=(1-t)*(a.re-contourAbscissa n)+t*(b.re-contourAbscissa n) := by ring
  rw [off]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
  have W := add_le_add (mul_le_mul_of_nonneg_left A (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left B ht.1)
  apply W.trans
  have H : contourSide e.1*((1-t)*a.im+t*b.im) ≤ |(1-t)*a.im+t*b.im| := by
    rcases e with ⟨s,k⟩; cases s
    · simpa [contourSide] using neg_le_abs ((1-t)*a.im+t*b.im)
    · simpa [contourSide] using le_abs_self ((1-t)*a.im+t*b.im)
  linear_combination 2*H

theorem edge_trig_decay (n : ℕ) (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge)
    {t : ℝ} (ht : t∈Icc 0 1) :
    ‖sixContourKernel (edgePoint n q (e,t))‖ ≤
      bentTrigConstant*Real.exp (-2*Real.pi*|(edgePoint n q (e,t)).im|) :=
  bent_trig_decay n _ (edge_cone n q hq e ht)

end OddZetaSix.B40a
