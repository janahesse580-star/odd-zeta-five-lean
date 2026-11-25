import OddZetaSix.B40a.Analysis.VandermondeContour

/-! Transfer a product-integrable upper bound on the normalized contour
integrand to a bound on the actual real determinant. -/
noncomputable section
namespace OddZetaSix.B40a
open Filter MeasureTheory Matrix Complex
open scoped Topology BigOperators

def bendVandermondeIntegrand (n : ℕ) (q : ℝ) (a : Fin (fiveRank n) → BendParam) : ℂ :=
  ((vandermonde (fun j => bendScaledSquare n q (a j))).det)^2 *
    ∏ j, bendWeight n q (a j)

/-- A finite-dimensional product bound suffices, with the correct factor
for contour normalization and determinant change of basis. -/
theorem det_bound_of_bend_majorant (n : ℕ) (hn : 0<n) (D : ℝ)
    (hmajor : ∀ᶠ q : ℕ in atTop, ∃ g : BendParam → ℝ,
      Integrable g bendMeasure ∧ (∫ x, g x ∂bendMeasure) = 1 ∧
      (∀ᵐ a ∂Measure.pi (fun _ : Fin (fiveRank n) => bendMeasure),
        ‖bendVandermondeIntegrand n q a‖ ≤ D * ∏ j, g (a j))) :
    ((fiveRank n).factorial : ℝ) * (2*Real.pi)^fiveRank n * |(fiveFunctional n).det|
      ≤ basisNormalization n * D := by
  have hlim := scaled_vandermonde_tendsto_actual n hn
  have hle : ∀ᶠ q : ℕ in atTop,
      ‖(basisNormalization n : ℂ) * ∫ a, bendVandermondeIntegrand n q a
        ∂Measure.pi (fun _ : Fin (fiveRank n) => bendMeasure)‖ ≤ basisNormalization n*D := by
    filter_upwards [hmajor] with q ⟨g,hg,hg1,hdom⟩
    have hi := (Integrable.fintype_prod (fun _ : Fin (fiveRank n) => hg)).const_mul D
    have hb := norm_integral_le_of_norm_le hi hdom
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (μ := fun _ : Fin (fiveRank n) => bendMeasure) (fun _ => g)] at hb
    simp only [hg1,Finset.prod_const_one,mul_one] at hb
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (basisNormalization_pos n hn)]
    exact mul_le_mul_of_nonneg_left hb (basisNormalization_pos n hn).le
  have h := le_of_tendsto hlim.norm hle
  have hreal : ((fiveFunctional n).map ofReal).det = ((fiveFunctional n).det : ℂ) :=
    (Complex.ofRealHom.map_det (fiveFunctional n)).symm
  rw [hreal, norm_mul,norm_mul,norm_pow,norm_neg,norm_mul,norm_mul,norm_I,mul_one,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,Complex.norm_natCast,
    abs_of_pos Real.pi_pos] at h
  rw [mul_assoc]
  simpa only [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] using h

/-- Passing from the complex-contour estimate to the required exponential
rate uses the exact normalization limit and the strict numerical gap. -/
theorem eventually_det_exp_of_bend_rate (E A : ℝ)
    (hgap : (12 : ℝ)/5+8/5*Real.log (5/8)+E < A)
    (hmajor : ∀ᶠ n : ℕ in atTop, ∀ᶠ q : ℕ in atTop, ∃ g : BendParam → ℝ,
      Integrable g bendMeasure ∧ (∫ x, g x ∂bendMeasure) = 1 ∧
      (∀ᵐ a ∂Measure.pi (fun _ : Fin (fiveRank n) => bendMeasure),
        ‖bendVandermondeIntegrand n q a‖ ≤ Real.exp (E*normalizer n) * ∏ j, g (a j))) :
    ∀ᶠ n : ℕ in atTop, |(fiveFunctional n).det| ≤ Real.exp (A*normalizer n) := by
  let ε := A-((12 : ℝ)/5+8/5*Real.log (5/8)+E)
  have hε : 0 < ε := sub_pos.mpr hgap
  filter_upwards [eventually_gt_atTop (0:ℕ),hmajor,basisNormalization_eventually_le ε hε]
    with n hn hmn hbn
  have hb := det_bound_of_bend_majorant n hn (Real.exp (E*normalizer n)) hmn
  have hv1 : (1:ℝ) ≤ ((fiveRank n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (fiveRank n)
  have hv2 : (1:ℝ) ≤ (2*Real.pi)^fiveRank n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hv := one_le_mul_of_one_le_of_one_le hv1 hv2
  calc
    |(fiveFunctional n).det| ≤
        ((fiveRank n).factorial : ℝ)*(2*Real.pi)^fiveRank n*|(fiveFunctional n).det| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hv (abs_nonneg (fiveFunctional n).det)
    _ ≤ _ := hb
    _ ≤ _ := mul_le_mul_of_nonneg_right hbn (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold ε; ring

end OddZetaSix.B40a
