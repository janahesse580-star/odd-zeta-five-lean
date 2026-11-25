import OddZetaSix.B40a.Analysis.PhaseCurvature
noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Set
theorem prim_horizontal (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun s=>primReal s y) (Real.log (x*x+y*y)/2) x := by
  have hq : 0<x*x+y*y := by nlinarith [sq_nonneg x, mul_self_pos.mpr hy.ne']
  have Q := (((hasDerivAt_id x).mul (hasDerivAt_id x)).add_const (y*y)).log hq.ne'
  have G := ((hasDerivAt_id x).div_const y).arctan
  have H := ((((hasDerivAt_id x).div_const 2).mul Q).sub (hasDerivAt_id x)).add (G.const_mul y)
  simp only [primReal,ite_eq_right hy.ne']
  apply H.congr_deriv
  simp only [Pi.mul_apply,id_eq,one_mul,mul_one]
  field_simp [hy.ne',hq.ne']
  <;> ring


/-- At height zero the horizontal primitive has a removable singularity in
value even where the horizontal logarithmic density is unbounded. -/
theorem prim_vertical_cont (x y : ℝ) : ContinuousAt (primReal x) y := by
  by_cases h : x=0
  · subst x
    have E : primReal 0=(fun _=>0) := by funext t; by_cases ht : t=0 <;> simp [primReal,ht]
    rw [E]; exact continuousAt_const
  · have hQ : 0<lineQ 0 x y := by simp [lineQ,lineX]; nlinarith only [sq_pos_of_ne_zero h,sq_nonneg y]
    have E : linePrim 0 x=primReal x := funext (fun t=>by simp [linePrim,lineX])
    exact E ▸ linePrim_cont_at 0 x y hQ

theorem prim_vertical_deriv (x y : ℝ) (hy : 0<y) :
    HasDerivAt (primReal x) (Real.arctan (x/y)) y := by
  have E : linePrim 0 x=primReal x := funext (fun t=>by simp [linePrim,lineX])
  simpa [E,lineX,lineD] using linePrim_deriv 0 x y hy.ne'

theorem prim_vertical_lipschitz (x y η : ℝ) (hy : 0≤y) (hη : 0<η) :
    |primReal x (y+η)-primReal x y| ≤ (Real.pi/2)*η := by
  obtain ⟨v,hv,E⟩ := exists_hasDerivAt_eq_slope (primReal x) (fun t=>Real.arctan (x/t))
    (by linarith : y<y+η) (fun t _=>(prim_vertical_cont x t).continuousWithinAt)
    (fun t ht=>prim_vertical_deriv x t (hy.trans_lt ht.1))
  rw [add_sub_cancel_left,eq_div_iff hη.ne'] at E
  rw [←E,abs_mul,abs_of_pos hη]
  apply mul_le_mul_of_nonneg_right _ hη.le
  exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le.trans_eq' (by ring), (Real.arctan_lt_pi_div_two _).le⟩

def sampleZ (x y : ℝ) : ℂ := (x:ℂ)+(y:ℂ)*Complex.I

theorem sample_sq (x y : ℝ) : ‖sampleZ x y‖^2=x*x+y*y := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]; simp [sampleZ]
theorem log_sample (x y : ℝ) : Real.log (x*x+y*y)/2=Real.log ‖sampleZ x y‖ := by
  rw [←sample_sq,Real.log_pow]; push_cast; ring
theorem sample_step (a b y : ℝ) : ‖sampleZ a y-sampleZ b y‖=|a-b| := by
  simp [sampleZ,←Complex.ofReal_sub]
theorem sample_vertical_le (x y η : ℝ) (hy : 0≤y) (hη : 0≤η) :
    ‖sampleZ x y‖≤‖sampleZ x (y+η)‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [sample_sq,sample_sq]
  nlinarith only [mul_nonneg hy hη,sq_nonneg η]
theorem sample_lower_y (x y : ℝ) : y≤‖sampleZ x y‖ := by
  exact (show y≤|y| from le_abs_self _).trans (by simpa [sampleZ] using Complex.abs_im_le_norm (sampleZ x y))
theorem sample_lower_x (x y : ℝ) : x≤‖sampleZ x y‖ := by
  exact (show x≤|x| from le_abs_self _).trans (by simpa [sampleZ] using Complex.abs_re_le_norm (sampleZ x y))

/-- The clipped-log Lipschitz estimate, valid between separated sample points. -/
theorem log_sample_step (a b y ρ : ℝ) (hρ : 0<ρ) (ha : ρ≤‖sampleZ a y‖) (hb : ρ≤‖sampleZ b y‖) :
    Real.log ‖sampleZ a y‖≤Real.log ‖sampleZ b y‖+|a-b|/ρ := by
  have H := circlePotential_le_add_dist 0 (sampleZ b y) (sampleZ a y) ρ hρ
  simpa only [circlePotential,sub_zero,max_eq_right ha,max_eq_right hb,sample_step] using H

/-- Upper quadrature for a numerator sample. The subdivision width and the
horizontal displacement can be chosen independently of the height. -/
theorem sample_upper (a y h η θ : ℝ) (hh : 0<h) (hy : 0≤y) (hη : 0<η) :
    ‖sampleZ (a+θ) y‖ ≤ Real.exp ((primReal (a+h) (y+η)-primReal a (y+η))/h+(|θ|+h)/η) := by
  have yp : 0<y+η := by linarith
  obtain ⟨v,hv,E⟩ := exists_hasDerivAt_eq_slope (fun x=>primReal x (y+η))
    (fun x=>Real.log (x*x+(y+η)*(y+η))/2) (by linarith : a<a+h)
    (fun x _=>(prim_horizontal x _ yp).continuousAt.continuousWithinAt) (fun x _=>prim_horizontal x _ yp)
  rw [add_sub_cancel_left,log_sample] at E
  have dist : |a+θ-v|≤|θ|+h := abs_le.mpr ⟨by linarith only [hv.2,neg_abs_le θ],by linarith only [hv.1,le_abs_self θ,hh]⟩
  have A : η≤‖sampleZ (a+θ) (y+η)‖ := (show η≤y+η by linarith).trans (sample_lower_y _ _)
  have B : η≤‖sampleZ v (y+η)‖ := (show η≤y+η by linarith).trans (sample_lower_y _ _)
  have H := log_sample_step (a+θ) v (y+η) η hη A B
  rw [E] at H
  apply (sample_vertical_le _ _ _ hy hη.le).trans
  rw [←Real.log_le_iff_le_exp (hη.trans_le A)]
  exact H.trans (add_le_add (le_refl _) (div_le_div_of_nonneg_right dist hη.le))
end OddZetaSix.B40a.Cert
