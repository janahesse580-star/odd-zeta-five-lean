import OddZetaSix.B40a.Analysis.PrimitiveVariation
noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Finset Set

private theorem prim_horizontal_nonneg {x y : ℝ} (hx : 0<x) (hy : 0≤y) :
    HasDerivAt (fun v=>primReal v y) (Real.log (x*x+y*y)/2) x := by
  rcases hy.eq_or_lt with rfl | hy
  · have h := (((hasDerivAt_id x).div_const 2).mul (((hasDerivAt_id x).mul (hasDerivAt_id x)).log
        (mul_ne_zero hx.ne' hx.ne'))).sub (hasDerivAt_id x)
    simp [primReal] at *
    apply h.congr_deriv
    field_simp [hx.ne']; ring
  · exact prim_horizontal x y hy

/-- Lower estimate for the denominator; its real part stays uniformly
positive. It also applies at y=0, where the contour meets the real line. -/
theorem sample_inverse_upper (a y h θ ρ : ℝ) (hh : 0<h) (hy : 0≤y)
    (hr : 0<ρ) (ha : ρ≤a) (hs : ρ≤a+θ) :
    ‖sampleZ (a+θ) y‖⁻¹ ≤ Real.exp (-(primReal (a+h) y-primReal a y)/h+(|θ|+h)/ρ) := by
  obtain ⟨v,hv,E⟩ := exists_hasDerivAt_eq_slope (fun x=>primReal x y)
    (fun x=>Real.log (x*x+y*y)/2) (by linarith : a<a+h)
    (fun x hx=>(prim_horizontal_nonneg (hr.trans_le (ha.trans hx.1)) hy).continuousAt.continuousWithinAt)
    (fun x hx=>prim_horizontal_nonneg (hr.trans_le (ha.trans hx.1.le)) hy)
  rw [add_sub_cancel_left,log_sample] at E
  have dist : |v-(a+θ)|≤|θ|+h := abs_le.mpr ⟨by linarith only [hv.1,le_abs_self θ,hh],by linarith only [hv.2,neg_abs_le θ]⟩
  have A := hs.trans (sample_lower_x (a+θ) y)
  have B := (ha.trans hv.1.le).trans (sample_lower_x v y)
  have H := (log_sample_step v (a+θ) y ρ hr B A).trans
    (add_le_add (le_refl _) (div_le_div_of_nonneg_right dist hr.le))
  rw [E] at H
  rw [←Real.log_le_iff_le_exp (inv_pos.mpr (hr.trans_le A)),Real.log_inv]
  linear_combination H

def sampledProduct (m : ℕ) (a y h θ : ℝ) :=
  ∏ j∈Finset.range m, ‖sampleZ (a+j*h+θ) y‖

private theorem product_upper_raised (m : ℕ) (a y h θ η : ℝ) (hh : 0<h) (hy : 0≤y) (hη : 0<η) :
    sampledProduct m a y h θ ≤ Real.exp ((primReal (a+m*h) (y+η)-primReal a (y+η))/h+
      m*((|θ|+h)/η)) := by
  induction m with
  | zero => simp [sampledProduct]
  | succ m ih =>
    have G := sample_upper (a+m*h) y h η θ hh hy hη
    have M := mul_le_mul ih G (norm_nonneg _) (Real.exp_pos _).le
    rw [←Real.exp_add] at M
    unfold sampledProduct at M ⊢
    rw [Finset.prod_range_succ]
    apply M.trans_eq; congr 1
    push_cast; rw [show a+(m+1)*h=a+m*h+h by ring]; ring

/-- A bound on a complete numerator block. The vertical smoothing error
occurs once per block, including a block crossing a real zero. -/
theorem product_upper (m : ℕ) (a y h θ η : ℝ) (hh : 0<h) (hy : 0≤y) (hη : 0<η) :
    sampledProduct m a y h θ ≤ Real.exp ((primReal (a+m*h) y-primReal a y+Real.pi*η)/h+
      m*((|θ|+h)/η)) := by
  have U := product_upper_raised m a y h θ η hh hy hη
  apply U.trans (Real.exp_le_exp.mpr (add_le_add _ (le_refl _)))
  apply div_le_div_of_nonneg_right _ hh.le
  have A := (abs_le.mp (prim_vertical_lipschitz a y η hy hη)).1
  have B := (abs_le.mp (prim_vertical_lipschitz (a+m*h) y η hy hη)).2
  linarith only [A,B]

theorem product_inverse_upper (m : ℕ) (a y h θ ρ : ℝ) (hh : 0<h) (hy : 0≤y)
    (hr : 0<ρ) (ha : ρ≤a) (hs : ρ≤a+θ) :
    (sampledProduct m a y h θ)⁻¹ ≤ Real.exp (-(primReal (a+m*h) y-primReal a y)/h+
      m*((|θ|+h)/ρ)) := by
  induction m with
  | zero => simp [sampledProduct]
  | succ m ih =>
    have pos : 0≤(m:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh.le
    have G := sample_inverse_upper (a+m*h) y h θ ρ hh hy hr (by linarith only [ha,pos]) (by linarith only [hs,pos])
    have M := mul_le_mul ih G (inv_nonneg.mpr (norm_nonneg _)) (Real.exp_pos _).le
    rw [←Real.exp_add] at M
    unfold sampledProduct at M ⊢
    rw [Finset.prod_range_succ,mul_inv_rev]
    rw [mul_comm]
    apply M.trans_eq; congr 1
    push_cast; rw [show a+(m+1)*h=a+m*h+h by ring]; ring

end OddZetaSix.B40a.Cert
