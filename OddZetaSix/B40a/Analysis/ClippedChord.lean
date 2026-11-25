import OddZetaSix.B40a.Analysis.Curvature
import OddZetaSix.B40a.Analysis.CirclePotential

noncomputable section
namespace OddZetaSix.B40a
open Set Real Filter
open scoped Topology

def radialAux (d t : ℝ) := Real.log (max d t)+(1/d^2)*t^2/2

private theorem radial_convex {d M : ℝ} (hd : 0<d) :
    ConvexOn ℝ (Icc 0 M) (radialAux d) := by
  let K := 1/d^2
  let quad := fun t : ℝ=>K*t^2/2
  have hK : 0≤K := by unfold K; positivity
  have hquad (t : ℝ) : HasDerivAt quad (K*t) t := by
    have H := (((hasDerivAt_id t).pow 2).const_mul (K/2))
    have he : quad=(fun x : ℝ=>K/2*(id^2) x) := by funext x; simp [quad]; ring
    rw [he]
    have hnum : K/2*((↑(2:ℕ):ℝ)*id t^(2-1:ℕ)*1)=K*t := by norm_num; ring
    rw [←hnum]
    exact H
  have hleft := convexOn_quadratic_of_lower_curvature (a:=0) (b:=d) (K:=K)
    (f:=fun _=>Real.log d) (df:=fun _=>0) (ddf:=fun _=>0)
    continuousOn_const (fun x _=>hasDerivAt_const x _) (fun x _=>hasDerivAt_const x _)
    (fun _ _=>by linarith only [hK])
  have rhs (t : ℝ) (hp : 0<t) : HasDerivAt (fun x=>x⁻¹) (-(t^2)⁻¹) t := by
    simpa using hasDerivAt_inv hp.ne'
  have hright := convexOn_quadratic_of_lower_curvature (a:=d) (b:=M) (K:=K)
    (f:=Real.log) (df:=fun t=>t⁻¹) (ddf:=fun t=> -(t^2)⁻¹)
    (Real.continuousOn_log.mono (fun t ht=>(hd.trans_le ht.1).ne'))
    (fun x hx=>Real.hasDerivAt_log (hd.trans hx.1).ne') (fun x hx=>rhs _ (hd.trans hx.1))
    (fun x hx=>by
      have H := one_div_le_one_div_of_le (sq_pos_of_pos hd) (pow_le_pow_left₀ hd.le hx.1.le 2)
      simpa [K,one_div] using neg_le_neg H)
  have hl : ConvexOn ℝ (Icc 0 d) (radialAux d) := hleft.congr (fun t ht=>by simp [radialAux,K,max_eq_left ht.2])
  have hr : ConvexOn ℝ (Icc d M) (radialAux d) := hright.congr (fun t ht=>by simp [radialAux,K,max_eq_right ht.1])
  apply convexOn_glue hl hr (L:=0+K*d) (R:=d⁻¹+K*d)
  · apply ((hasDerivAt_const d (Real.log d)).add (hquad d)).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp [radialAux,quad,K,max_eq_left (le_of_lt (show x<d from hx))]
    · simp [radialAux,quad,K]
  · apply ((Real.hasDerivAt_log hd.ne').add (hquad d)).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp [radialAux,quad,K,max_eq_right (le_of_lt (show d<x from hx))]
    · simp [radialAux,quad,K]
  · linarith [inv_pos.mpr hd]

private theorem radial_mono {d t v : ℝ} (hd : 0<d) (ht : 0≤t) (htv : t≤v) :
    radialAux d t ≤ radialAux d v :=
  add_le_add (Real.log_le_log (hd.trans_le (le_max_left _ _)) (max_le_max_left _ htv))
    (by apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htv 2) (by positivity))

private theorem combo_sq (z w : ℂ) (a b : ℝ) (hab : a+b=1) :
    a*‖z‖^2+b*‖w‖^2-‖a • z+b • w‖^2=a*b*‖z-w‖^2 := by
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero]
  rw [show a=1-b by linarith]; ring

/-- The clipped logarithm plus a quadratic is globally convex on the plane.
No count, transversality or derivatives of the circle crossings are needed. -/
theorem clipped_chord (z w : ℂ) {d a b : ℝ} (hd : 0<d) (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    Real.log (max d ‖a • z+b • w‖) ≤ a*Real.log (max d ‖z‖)+b*Real.log (max d ‖w‖)+
      a*b*‖z-w‖^2/(2*d^2) := by
  let M := max ‖z‖ ‖w‖
  have H := (radial_convex (M:=M) hd).2 (show ‖z‖∈Icc 0 M from ⟨norm_nonneg _,le_max_left _ _⟩)
    (show ‖w‖∈Icc 0 M from ⟨norm_nonneg _,le_max_right _ _⟩) ha hb hab
  simp only [smul_eq_mul] at H
  have N := norm_add_le (a • z) (b • w)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at N
  -- Apply radial convexity to the actual averaged vector. Applying the
  -- scalar chord alone would lose the angular part of the quadratic.
  have B := (radial_mono hd (norm_nonneg _) N).trans H
  unfold radialAux at B
  have V := combo_sq z w a b hab
  have E : (1/d^2)*(a*‖z‖^2+b*‖w‖^2-‖a • z+b • w‖^2)/2=a*b*‖z-w‖^2/(2*d^2) := by rw [V]; ring
  linarith only [B,E]

/-- For a squared affine contour the drift from its chord is explicit. -/
theorem clipped_square_chord (z w u : ℂ) {d a b : ℝ} (hd : 0<d)
    (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    circlePotential u d ((a • z+b • w)^2) ≤
      a*circlePotential u d (z^2)+b*circlePotential u d (w^2)+
      a*b*(‖z^2-w^2‖^2/(2*d^2)+‖z-w‖^2/d) := by
  have add_eq : a • (z^2-u)+b • (w^2-u)=(a • z^2+b • w^2)-u := by
    simp only [Complex.real_smul]
    rw [show (a:ℂ)=1-b by exact_mod_cast (show a=1-b by linarith)]; ring
  have drift : (a • z+b • w)^2-(a • z^2+b • w^2)= -((a:ℂ)*b)*(z-w)^2 := by
    simp only [Complex.real_smul]
    rw [show (a:ℂ)=1-b by exact_mod_cast (show a=1-b by linarith)]; ring
  have C := clipped_chord (z^2-u) (w^2-u) hd ha hb hab
  rw [add_eq,sub_sub_sub_cancel_right] at C
  have L := circlePotential_le_add_dist u (a • z^2+b • w^2) ((a • z+b • w)^2) d hd
  rw [drift,norm_mul,norm_neg,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at L
  unfold circlePotential at L ⊢
  apply L.trans
  apply le_trans (add_le_add_left C _)
  apply le_of_eq; ring

end OddZetaSix.B40a
