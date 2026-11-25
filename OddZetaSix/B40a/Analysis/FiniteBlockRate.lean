import OddZetaSix.B40a.Analysis.BlockQuadrature
import OddZetaSix.B40a.Analysis.Normalization
noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Finset Polynomial

def blockField (a y w : ℝ) := primReal (a+w) y-primReal a y-w*(Real.log w-1)
def normalizedBlock (m : ℕ) (D a y θ : ℝ) :=
  (D^m/(m.factorial:ℝ))*sampledProduct m a y (1/D) θ

private theorem scaled_factorial_log (m : ℕ) (D w : ℝ) (hD : 0<D) (hw : 0<w) (hm : (m:ℝ)=D*w) :
    Real.log (D^m/(m.factorial:ℝ))≤ -D*w*(Real.log w-1) ∧
    Real.log (D^m/(m.factorial:ℝ))⁻¹≤D*w*(Real.log w-1)+1+Real.log (m:ℝ) := by
  have H := block_factorial_log m
  have hf : (0:ℝ)<m.factorial := by exact_mod_cast m.factorial_pos
  have l : Real.log (m:ℝ)=Real.log D+Real.log w := by rw [hm,Real.log_mul hD.ne' hw.ne']
  rw [Real.log_inv,Real.log_div (pow_ne_zero m hD.ne') hf.ne',Real.log_pow]
  rw [l] at H
  constructor <;> nlinarith only [H.1,H.2,congrArg (fun x : ℝ=>x*Real.log w) hm,hm,l]

theorem normalized_upper (m : ℕ) (D a y θ w η : ℝ) (hD : 0<D) (hy : 0≤y)
    (hw : 0<w) (hm : (m:ℝ)=D*w) (hη : 0<η) :
    normalizedBlock m D a y θ ≤ Real.exp (D*(blockField a y w+Real.pi*η)+m*((|θ|+1/D)/η)) := by
  have H := product_upper m a y (1/D) θ η (by positivity) hy hη
  have hw' : (m:ℝ)*(1/D)=w := by rw [hm]; field_simp
  rw [hw'] at H
  have G := Real.le_exp_of_log_le (scaled_factorial_log m D w hD hw hm).1
  apply (mul_le_mul G H (by unfold sampledProduct; positivity) (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]; congr 1; unfold blockField; simp only [div_eq_mul_inv,one_mul,inv_inv]; ring

theorem normalized_inverse (m : ℕ) (D a y θ w ρ : ℝ) (hD : 0<D) (hy : 0≤y)
    (hw : 0<w) (hm : (m:ℝ)=D*w) (hr : 0<ρ) (ha : ρ≤a) (hs : ρ≤a+θ) :
    (normalizedBlock m D a y θ)⁻¹ ≤ Real.exp (-D*blockField a y w+
      (1+Real.log (m:ℝ))+m*((|θ|+1/D)/ρ)) := by
  have H := product_inverse_upper m a y (1/D) θ ρ (by positivity) hy hr ha hs
  have hw' : (m:ℝ)*(1/D)=w := by rw [hm]; field_simp
  rw [hw'] at H
  have G := Real.le_exp_of_log_le (scaled_factorial_log m D w hD hw hm).2
  unfold normalizedBlock; rw [mul_inv_rev,mul_comm]
  apply (mul_le_mul G H (by unfold sampledProduct; positivity) (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]; congr 1; unfold blockField; simp only [div_eq_mul_inv,one_mul,inv_inv]; ring

/-- Exact identification with the polynomial rising factorial, before applying
any estimate. The conjugate half-contour has the same product of norms. -/
theorem rising_eq_sampled (m : ℕ) (q : ℚ) (z : ℂ) (D a y θ : ℝ) (hD : 0<D)
    (hr : z.re+(q:ℝ)=D*(a+θ)) (hi : |z.im|=D*y) :
    ‖aeval z (rising q m)‖=D^m*sampledProduct m a y (1/D) θ := by
  have term (j : ℕ) : ‖z+((q:ℂ)+j)‖=D*‖sampleZ (a+j*(1/D)+θ) y‖ := by
    have im2 := congrArg (fun v : ℝ=>v^2) hi
    change |z.im|^2=(D*y)^2 at im2; rw [sq_abs] at im2
    have nr : (z+((q:ℂ)+j)).re=D*(a+θ)+j := by simp [Complex.add_re]; linarith
    have ni : (z+((q:ℂ)+j)).im=z.im := by simp
    apply le_antisymm
    all_goals
      apply le_of_sq_le_sq _ (by positivity)
      simp only [mul_pow,sample_sq,←Complex.normSq_eq_norm_sq (z+((q:ℂ)+j)),Complex.normSq_apply,nr,ni]
      apply le_of_eq
      field_simp [hD.ne']
      nlinarith only [im2]
  unfold rising sampledProduct
  simp only [map_prod,map_add,aeval_X,aeval_C,Complex.norm_prod]
  simp only [map_natCast]
  calc
    _ = ∏ j ∈ range m, D*‖sampleZ (a+j*(1/D)+θ) y‖ := by
      apply Finset.prod_congr rfl; intro j hj; exact term j
    _ = _ := by rw [Finset.prod_mul_distrib]; simp
end OddZetaSix.B40a.Cert
