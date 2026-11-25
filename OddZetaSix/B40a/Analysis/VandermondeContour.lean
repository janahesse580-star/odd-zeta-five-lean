import OddZetaSix.B40a.Analysis.ContourMoment
import OddZetaSix.B40a.Analysis.Normalization

/-! The scaled squared Vandermonde integral for the actual B40a determinant. -/
noncomputable section
namespace OddZetaSix.B40a
open Matrix Polynomial Finset Filter MeasureTheory Complex
open scoped BigOperators Topology

def bendScaledSquare (n : ℕ) (q : ℝ) (a : BendParam) : ℂ :=
  ((edgePoint n q a + ((center n : ℕ) : ℂ))/(50*(n : ℂ)))^2

private def scaledChange (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℂ :=
  fun i j => ((inSquareBasis i.val).coeff j.val : ℂ)*(50*(n : ℂ))^(2*j.val)

private theorem sampleMatrix_basis_change (n : ℕ) (hn : 0 < n) (q : ℝ)
    (a : Fin (fiveRank n) → BendParam) :
    sampleMatrix (bendBasis n q) a =
      scaledChange n * (vandermonde (fun j => bendScaledSquare n q (a j))).transpose := by
  ext i j
  unfold sampleMatrix bendBasis
  rw [evenBasis_expand n i, map_sum]
  simp only [Polynomial.smul_eq_C_mul,map_mul,aeval_C,map_pow,aeval_X,
    Matrix.mul_apply,scaledChange,transpose_apply,vandermonde,Matrix.of_apply,bendScaledSquare]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (50 : ℂ)*(n : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne')
  rw [← pow_mul,div_pow]
  rw [mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
  rfl

private theorem squareScaling_eq_leadingCoeff (i : ℕ) :
    squareScaling i = (evenBasis i).leadingCoeff := by
  cases i with
  | zero => simp [squareScaling]
  | succ i => simp [squareScaling,evenBasis_leadingCoeff_succ]

theorem sampleMatrix_det_sq (n : ℕ) (hn : 0 < n) (q : ℝ)
    (a : Fin (fiveRank n) → BendParam) :
    (sampleMatrix (bendBasis n q) a).det^2 =
      (basisNormalization n : ℂ) * ((vandermonde (fun j => bendScaledSquare n q (a j))).det)^2 := by
  rw [sampleMatrix_basis_change n hn,det_mul,det_transpose,mul_pow]
  have htri : (scaledChange n).IsLowerTriangular := by
    intro i j hij
    unfold scaledChange
    rw [coeff_eq_zero_of_natDegree_lt (by rwa [inSquareBasis_degree]),Rat.cast_zero,zero_mul]
  rw [Matrix.det_of_isLowerTriangular _ htri,← Finset.prod_pow]
  unfold basisNormalization
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [scaledChange,inSquareBasis_diag_coeff,squareScaling_eq_leadingCoeff,mul_pow,← pow_mul]
  rw [show (2*i.val)*2 = 4*i.val by omega]

theorem det_bendMatrix_scaled_vandermonde (n : ℕ) (hn : 0<n) (q : ℝ)
    (hq : bendNodeY n 7 ≤ q) :
    ((fiveRank n).factorial : ℂ)*(bendMatrix n q).det =
      (basisNormalization n : ℂ) *
      ∫ a : Fin (fiveRank n) → BendParam,
        ((vandermonde (fun j => bendScaledSquare n q (a j))).det)^2 * ∏ j, bendWeight n q (a j)
        ∂Measure.pi (fun _ => bendMeasure) := by
  rw [det_bendMatrix_integral n q hq,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  rw [sampleMatrix_det_sq n hn, mul_assoc]

/-- The exact large-height limit of the normalized many-variable contour integral. -/
theorem scaled_vandermonde_tendsto_actual (n : ℕ) (hn : 0<n) :
    Tendsto (fun q : ℕ => (basisNormalization n : ℂ) *
      ∫ a : Fin (fiveRank n) → BendParam,
        ((vandermonde (fun j => bendScaledSquare n q (a j))).det)^2 * ∏ j, bendWeight n q (a j)
        ∂Measure.pi (fun _ => bendMeasure)) atTop
      (𝓝 (((fiveRank n).factorial : ℂ)*((-(2*(Real.pi : ℂ)*Complex.I))^fiveRank n *
        ((fiveFunctional n).map ofReal).det))) := by
  apply ((det_bendMatrix_tendsto n).const_mul ((fiveRank n).factorial : ℂ)).congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (bendNodeY n 7))] with q hq
  exact det_bendMatrix_scaled_vandermonde n hn q hq

end OddZetaSix.B40a
