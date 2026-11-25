import OddZetaSix.B40a.Analysis.ComplexKernel

/-! Upward half-integer contour for B40a, with the full entrywise residue identity.
The analytic estimates and residue proof adapt the MIT-licensed upstream SixContour module. -/
noncomputable section
set_option autoImplicit false
namespace OddZetaSix.B40a
open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

/-- Half-integer vertical contour abscissa at minus floor(17n/20) minus one half. -/
def contourAbscissa (n : ℕ) : ℝ := -(anchor n : ℝ) - 1 / 2

/-- Point on the vertical contour at height `y`. -/
def contourPoint (n : ℕ) (y : ℝ) : ℂ :=
  (contourAbscissa n : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem contourPoint_re (n : ℕ) (y : ℝ) :
    (contourPoint n y).re = contourAbscissa n := by
  simp [contourPoint]

@[simp] theorem contourPoint_im (n : ℕ) (y : ℝ) :
    (contourPoint n y).im = y := by
  simp [contourPoint]

theorem contourAbscissa_in_halfplane (n : ℕ) :
    -(34*(n : ℝ)+1)<contourAbscissa n := by
  have h : (anchor n : ℝ) ≤ (n : ℝ) := by exact_mod_cast anchor_le n
  unfold contourAbscissa
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem contourAbscissa_ne_int (n : ℕ) (m : ℤ) :
    contourAbscissa n ≠ (m : ℝ) := OddZetaSix.sixContourAbscissa_ne_int (anchor n) m

theorem contourPoint_eq_upstream (n : ℕ) (y : ℝ) :
    contourPoint n y = OddZetaSix.sixContourPoint (anchor n) y := rfl

def contourIntegrand (n i j : ℕ) (z : ℂ) : ℂ :=
  entryComplex n i j z * sixContourKernel z

theorem contourIntegrand_analyticAt (n i j : ℕ) (z : ℂ)
    (hz : -(34*(n : ℝ)+1)<z.re) (h : Complex.sin ((Real.pi : ℂ)*z) ≠ 0) :
    AnalyticAt ℂ (contourIntegrand n i j) z :=
  (entryComplex_analyticAt n i j z hz).mul (sixContourKernel_analyticAt z h)

def polynomialCoefficientNorm (P : ℚ[X]) : ℝ :=
  ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖

def entryCoefficientNorm (n i j : ℕ) : ℝ :=
  polynomialCoefficientNorm
    (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j)

def contourDecayRadius (n : ℕ) : ℝ := 2 * (84 * (n : ℝ) + 1)

def contourDecayConstant (n : ℕ) : ℝ :=
  2 ^ (500 * n + 12) *
    (1 + ∑ i : Fin (fiveRank n), ∑ j : Fin (fiveRank n), entryCoefficientNorm n i j)

theorem contourDecayRadius_ge_two (n : ℕ) : 2 ≤ contourDecayRadius n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [contourDecayRadius]; linarith

private theorem entryCoefficientNorm_nonneg (n i j : ℕ) :
    0 ≤ entryCoefficientNorm n i j := by
  unfold entryCoefficientNorm polynomialCoefficientNorm
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem contourDecayConstant_pos (n : ℕ) : 0 < contourDecayConstant n := by
  unfold contourDecayConstant
  apply mul_pos (by positivity)
  have h : 0 ≤ ∑ i : Fin (fiveRank n), ∑ j : Fin (fiveRank n), entryCoefficientNorm n i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      entryCoefficientNorm_nonneg n i j
  linarith

private theorem norm_aeval_le_coefficientNorm (P : ℚ[X]) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖aeval z P‖ ≤ polynomialCoefficientNorm P * ‖z‖ ^ P.natDegree := by
  rw [aeval_eq_sum_range]
  calc
    _ ≤ ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖ * ‖z‖ ^ r := by
      simpa [Algebra.smul_def, norm_mul, norm_pow] using
        norm_sum_le (range (P.natDegree + 1)) (fun r => P.coeff r • z ^ r)
    _ ≤ ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖ * ‖z‖ ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hz (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

private theorem six_sum_pole_orders (n : ℕ) :
    (∑ k ∈ kernelPoleSet n, kernelPoleOrder n k) = 500 * n + 12 := by
  have h := congrArg Polynomial.natDegree (kernel_denominator_powers n)
  rw [kernelDenominator_degree,
    natDegree_prod_of_monic _ _ (fun (k : ℕ) _ =>
      (monic_X_add_C (k : ℚ)).pow (kernelPoleOrder n k))] at h
  simpa only [natDegree_pow, natDegree_X_add_C, mul_one] using h.symm

private theorem six_denominator_norm_lower (n : ℕ) (z : ℂ)
    (hz : contourDecayRadius n ≤ ‖z‖) :
    (‖z‖ / 2) ^ (500 * n + 12) ≤ ‖aeval z (kernelDenominator n)‖ := by
  rw [kernel_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast, norm_prod, norm_pow]
  rw [← six_sum_pole_orders n, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by positivity) _)
  intro k hk
  apply pow_le_pow_left₀ (by positivity)
  have hk' : (k : ℝ) ≤ 84 * (n : ℝ) + 1 := by exact_mod_cast (kernel_pole_address_bounds n k hk).2
  have ht : ‖z‖ ≤ ‖z + (k : ℂ)‖ + (k : ℝ) := by
    simpa only [add_sub_cancel_right, Complex.norm_natCast] using norm_sub_le (z + (k : ℂ)) k
  dsimp [contourDecayRadius] at hz
  linarith

private theorem six_entry_numerator_degree_decay (n : ℕ) (i j : Fin (fiveRank n)) :
    (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j).natDegree +
      (90 * n + 15) ≤ 500 * n + 12 := by
  rw [natDegree_mul
    (mul_ne_zero (by simpa using kernelNormalization_ne_zero n) (kernelNumerator_monic n).ne_zero)
    (centeredMultiplier_ne_zero n i j), natDegree_C_mul (kernelNormalization_ne_zero n),
    kernelNumerator_degree, centeredMultiplier_degree]
  have hi : i.val < 40 * n := i.isLt
  have hj : j.val < 40 * n := j.isLt
  omega

theorem entryComplex_norm_le_decay (n : ℕ) (i j : Fin (fiveRank n)) (z : ℂ)
    (hz : contourDecayRadius n ≤ ‖z‖) :
    ‖entryComplex n i j z‖ ≤ contourDecayConstant n / ‖z‖ ^ (90 * n + 15) := by
  let P := C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j
  let A := entryCoefficientNorm n i j
  have hx : 1 ≤ ‖z‖ := le_trans (by norm_num : (1 : ℝ) ≤ 2)
    ((contourDecayRadius_ge_two n).trans hz)
  have hxpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hx
  have hA : 0 ≤ A := entryCoefficientNorm_nonneg n i j
  have hN : ‖aeval z P‖ ≤ A * ‖z‖ ^ P.natDegree := norm_aeval_le_coefficientNorm P z hx
  have hd := six_entry_numerator_degree_decay n i j
  have hDlow := six_denominator_norm_lower n z hz
  have hDpos : 0 < ‖aeval z (kernelDenominator n)‖ :=
    lt_of_lt_of_le (pow_pos (by positivity) _) hDlow
  have hAtot : A ≤ 1 + ∑ a : Fin (fiveRank n), ∑ b : Fin (fiveRank n), entryCoefficientNorm n a b := by
    have h1 : A ≤ ∑ b : Fin (fiveRank n), entryCoefficientNorm n i b :=
      Finset.single_le_sum (f := fun b : Fin (fiveRank n) => entryCoefficientNorm n i b)
        (fun b _ => entryCoefficientNorm_nonneg n i b) (Finset.mem_univ j)
    have h2 : (∑ b : Fin (fiveRank n), entryCoefficientNorm n i b) ≤
        ∑ a : Fin (fiveRank n), ∑ b : Fin (fiveRank n), entryCoefficientNorm n a b :=
      Finset.single_le_sum
        (f := fun a : Fin (fiveRank n) => ∑ b : Fin (fiveRank n), entryCoefficientNorm n a b)
        (fun a _ => Finset.sum_nonneg fun b _ => entryCoefficientNorm_nonneg n a b) (Finset.mem_univ i)
    linarith
  rw [entryComplex, norm_div]
  apply (div_le_div_iff₀ hDpos (pow_pos hxpos _)).mpr
  change ‖aeval z P‖ * ‖z‖ ^ (90 * n + 15) ≤ _
  calc
    _ ≤ (A * ‖z‖ ^ P.natDegree) * ‖z‖ ^ (90 * n + 15) :=
      mul_le_mul_of_nonneg_right hN (pow_nonneg (norm_nonneg _) _)
    _ = A * ‖z‖ ^ (P.natDegree + (90 * n + 15)) := by rw [pow_add]; ring
    _ ≤ A * ‖z‖ ^ (500 * n + 12) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hd) hA
    _ = (2 ^ (500 * n + 12) * A) * (‖z‖ / 2) ^ (500 * n + 12) := by rw [div_pow]; field_simp
    _ ≤ contourDecayConstant n * (‖z‖ / 2) ^ (500 * n + 12) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAtot (by positivity))
        (pow_nonneg (by positivity) _)
    _ ≤ contourDecayConstant n * ‖aeval z (kernelDenominator n)‖ :=
      mul_le_mul_of_nonneg_left hDlow (contourDecayConstant_pos n).le

def contourIntegrandDecayConstant (n : ℕ) : ℝ :=
  4 * Real.pi ^ 5 * contourDecayConstant n

theorem contourIntegrandDecayConstant_pos (n : ℕ) :
    0 < contourIntegrandDecayConstant n :=
  mul_pos (by positivity) (contourDecayConstant_pos n)

theorem contourIntegrand_norm_le_decay (n : ℕ) (i j : Fin (fiveRank n)) (z : ℂ)
    (hz : contourDecayRadius n ≤ ‖z‖)
    (hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖contourIntegrand n i j z‖ ≤
      contourIntegrandDecayConstant n / ‖z‖ ^ (90 * n + 15) := by
  rw [contourIntegrand, norm_mul]
  calc
    _ ≤ (contourDecayConstant n / ‖z‖ ^ (90 * n + 15)) * (4 * Real.pi ^ 5) :=
      mul_le_mul (entryComplex_norm_le_decay n i j z hz)
        (sixContourKernel_norm_le z hs) (norm_nonneg _)
        (div_nonneg (contourDecayConstant_pos n).le (pow_nonneg (norm_nonneg _) _))
    _ = _ := by unfold contourIntegrandDecayConstant; ring

/-- Upward-oriented vertical contour integrand on `Re z = -n - 1/2`. -/
def verticalIntegrand (n i j : ℕ) (y : ℝ) : ℂ :=
  contourIntegrand n i j (contourPoint n y) * Complex.I

theorem verticalIntegrand_continuous (n i j : ℕ) :
    Continuous (verticalIntegrand n i j) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have ha := contourIntegrand_analyticAt n i j (contourPoint n y)
    (by simpa using contourAbscissa_in_halfplane n) (six_sin_ne_zero_on_contour (anchor n) y)
  exact (ha.continuousAt.comp (by unfold contourPoint; fun_prop)).mul continuousAt_const

theorem verticalIntegrand_integrable (n : ℕ) (i j : Fin (fiveRank n)) :
    Integrable (verticalIntegrand n i j) := by
  let g : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  have hbound : ∀ y : ℝ, contourDecayRadius n ≤ |y| →
      ‖verticalIntegrand n i j y‖ ≤ (2 * contourIntegrandDecayConstant n) * ‖g y‖ := by
    intro y hy
    have hy1 : 1 ≤ |y| := (by norm_num : (1 : ℝ) ≤ 2).trans ((contourDecayRadius_ge_two n).trans hy)
    have hr : |y| ≤ ‖contourPoint n y‖ := by
      simpa [contourPoint] using Complex.abs_im_le_norm (contourPoint n y)
    have hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * contourPoint n y)‖ := by
      apply six_sin_norm_ge_one_half_integer (-(anchor n : ℤ) - 1)
      simp only [contourPoint_re, contourAbscissa]; push_cast; ring
    have hdec : ‖verticalIntegrand n i j y‖ ≤
        contourIntegrandDecayConstant n / |y| ^ (90 * n + 15) := by
      rw [verticalIntegrand, norm_mul, Complex.norm_I, mul_one]
      exact (contourIntegrand_norm_le_decay n i j _ (hy.trans hr) hs).trans
        (div_le_div_of_nonneg_left (contourIntegrandDecayConstant_pos n).le
          (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) hr _))
    have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y]
    have hp : y ^ 2 ≤ |y| ^ (90 * n + 15) := by
      rw [← sq_abs y]; exact pow_le_pow_right₀ hy1 (by omega)
    have hden : 0 < 1 + y ^ 2 := by positivity
    calc
      ‖verticalIntegrand n i j y‖
          ≤ contourIntegrandDecayConstant n / |y| ^ (90 * n + 15) := hdec
      _ ≤ (2 * contourIntegrandDecayConstant n) / (1 + y ^ 2) := by
        rw [div_le_div_iff₀ (pow_pos (by linarith) _) hden]
        have hC := (contourIntegrandDecayConstant_pos n).le
        nlinarith
      _ = (2 * contourIntegrandDecayConstant n) * ‖g y‖ := by
        simp only [g, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
  have htop : verticalIntegrand n i j =O[atTop] g :=
    Asymptotics.isBigO_iff.mpr ⟨2 * contourIntegrandDecayConstant n,
      (eventually_ge_atTop (contourDecayRadius n)).mono fun y hy =>
        hbound y (hy.trans (le_abs_self y))⟩
  have hbot : verticalIntegrand n i j =O[atBot] g :=
    Asymptotics.isBigO_iff.mpr ⟨2 * contourIntegrandDecayConstant n,
      (eventually_le_atBot (-contourDecayRadius n)).mono fun y hy =>
        hbound y (by linarith [neg_le_abs y])⟩
  exact (verticalIntegrand_continuous n i j).locallyIntegrable
    |>.integrable_of_isBigO_atBot_atTop hbot (integrable_inv_one_add_sq.integrableAtFilter _)
      htop (integrable_inv_one_add_sq.integrableAtFilter _)

def verticalIntegral (n i j : ℕ) : ℂ := ∫ y : ℝ, verticalIntegrand n i j y

def verticalTruncation (n i j : ℕ) (q : ℝ) : ℂ :=
  ∫ y in -q..q, verticalIntegrand n i j y

def horizontalClosingIntegral (n i j q : ℕ) (y : ℝ) : ℂ :=
  ∫ x in contourAbscissa n..((q : ℝ) + 1 / 2),
    contourIntegrand n i j ((x : ℂ) + (y : ℂ) * Complex.I)

def rightClosingIntegral (n i j q : ℕ) : ℂ :=
  ∫ y in -(q : ℝ)..(q : ℝ),
    contourIntegrand n i j (((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I) * Complex.I

def clockwiseRectangleIntegral (n i j q : ℕ) : ℂ :=
  verticalTruncation n i j q +
    horizontalClosingIntegral n i j q q -
    rightClosingIntegral n i j q -
    horizontalClosingIntegral n i j q (-q)

private theorem edge_bound_simplify (n : ℕ) (r : ℝ) (hr : 0 < r) :
    contourIntegrandDecayConstant n / r ^ (90 * n + 15) * (2 * r) =
      2 * contourIntegrandDecayConstant n / r ^ (90 * n + 14) := by
  rw [show 90 * n + 15 = (90 * n + 14) + 1 by omega, pow_succ]
  field_simp

private theorem integrand_norm_le_of_radius (n : ℕ) (i j : Fin (fiveRank n))
    (z : ℂ) (r : ℝ) (hr : contourDecayRadius n ≤ r) (hz : r ≤ ‖z‖)
    (hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖contourIntegrand n i j z‖ ≤
      contourIntegrandDecayConstant n / r ^ (90 * n + 15) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((contourDecayRadius_ge_two n).trans hr)
  exact (contourIntegrand_norm_le_decay n i j z (hr.trans hz) hs).trans
    (div_le_div_of_nonneg_left (contourIntegrandDecayConstant_pos n).le
      (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hz _))

theorem clockwiseRectangleIntegral_tendsto (n : ℕ) (i j : Fin (fiveRank n)) :
    Tendsto (fun q : ℕ => clockwiseRectangleIntegral n i j q) atTop
      (𝓝 (verticalIntegral n i j)) := by
  have hvert : Tendsto (fun q : ℕ => verticalTruncation n i j q) atTop
      (𝓝 (verticalIntegral n i j)) :=
    (intervalIntegral_tendsto_integral (verticalIntegrand_integrable n i j)
      tendsto_neg_atTop_atBot tendsto_id).comp tendsto_natCast_atTop_atTop
  have hhor : ∀ (y : ℕ → ℝ), (∀ q, |y q| = q) →
      Tendsto (fun q : ℕ => horizontalClosingIntegral n i j q (y q)) atTop (𝓝 0) := by
    intro y hy
    apply squeeze_zero_norm' (a := fun q : ℕ =>
      2 * contourIntegrandDecayConstant n / (q : ℝ) ^ (90 * n + 14))
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (contourDecayRadius n))] with q hq
      have hq2 : (2 : ℝ) ≤ q := (contourDecayRadius_ge_two n).trans hq
      have hq0 : (0 : ℝ) < q := by linarith
      have hlen : |((q : ℝ) + 1 / 2) - contourAbscissa n| ≤ 2 * (q : ℝ) := by
        have ha : (anchor n : ℝ) ≤ (n : ℝ) := by exact_mod_cast anchor_le n
        dsimp [contourAbscissa, contourDecayRadius] at *
        rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) (anchor n)])]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc
        ‖horizontalClosingIntegral n i j q (y q)‖
            ≤ (contourIntegrandDecayConstant n / (q : ℝ) ^ (90 * n + 15)) *
                |((q : ℝ) + 1 / 2) - contourAbscissa n| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro x _
              apply integrand_norm_le_of_radius n i j _ (q : ℝ) hq
              · simpa [hy q] using Complex.abs_im_le_norm ((x : ℂ) + (y q : ℂ) * Complex.I)
              · apply six_sin_norm_ge_one_of_im
                simpa [hy q] using (show (1 : ℝ) ≤ q by linarith)
        _ ≤ (contourIntegrandDecayConstant n / (q : ℝ) ^ (90 * n + 15)) * (2 * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hlen
            (div_nonneg (contourIntegrandDecayConstant_pos n).le (pow_nonneg (Nat.cast_nonneg q) _))
        _ = _ := edge_bound_simplify n q hq0
    · exact tendsto_const_div_pow _ _ (by omega)
  have hright : Tendsto (fun q : ℕ => rightClosingIntegral n i j q) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun q : ℕ =>
      2 * contourIntegrandDecayConstant n / (q : ℝ) ^ (90 * n + 14))
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (contourDecayRadius n))] with q hq
      have hq2 : (2 : ℝ) ≤ q := (contourDecayRadius_ge_two n).trans hq
      have hq0 : (0 : ℝ) < q := by linarith
      calc
        ‖rightClosingIntegral n i j q‖
            ≤ (contourIntegrandDecayConstant n / (q : ℝ) ^ (90 * n + 15)) *
                |(q : ℝ) - -(q : ℝ)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro y _
              rw [norm_mul, Complex.norm_I, mul_one]
              apply integrand_norm_le_of_radius n i j _ (q : ℝ) hq
              · have h : (q : ℝ) + 1 / 2 ≤ ‖((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I‖ := by
                  simpa using Complex.re_le_norm (((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I)
                linarith
              · exact six_sin_norm_ge_one_half_integer (q : ℤ) _ (by simp)
        _ = _ := by
          rw [show |(q : ℝ) - -(q : ℝ)| = 2 * (q : ℝ) by
            rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]; ring]
          exact edge_bound_simplify n q hq0
    · exact tendsto_const_div_pow _ _ (by omega)
  have htop := hhor (fun q => (q : ℝ)) (fun q => by simp)
  have hbot := hhor (fun q => -(q : ℝ)) (fun q => by simp)
  simpa only [clockwiseRectangleIntegral, add_zero, sub_zero] using
    ((hvert.add htop).sub hright).sub hbot

private def sixRectBoundary (a b h : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + (-h : ℝ) * I)) -
    (∫ x in a..b, f ((x : ℂ) + (h : ℂ) * I)) +
    (∫ y in -h..h, f ((b : ℂ) + (y : ℂ) * I) * I) -
    (∫ y in -h..h, f ((a : ℂ) + (y : ℂ) * I) * I)

private theorem horizontal_primitive (F f : ℂ → ℂ) (a b y : ℝ)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt F (f ((x : ℂ) + (y : ℂ) * I))
      ((x : ℂ) + (y : ℂ) * I))
    (hi : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume a b) :
    (∫ x in a..b, f ((x : ℂ) + (y : ℂ) * I)) =
      F ((b : ℂ) + (y : ℂ) * I) - F ((a : ℂ) + (y : ℂ) * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro x hx
  simpa using ((hd x hx).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))).comp_ofReal

private theorem vertical_primitive (F f : ℂ → ℂ) (a h : ℝ)
    (hd : ∀ y ∈ uIcc (-h) h, HasDerivAt F (f ((a : ℂ) + (y : ℂ) * I))
      ((a : ℂ) + (y : ℂ) * I))
    (hi : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I) * I) volume (-h) h) :
    (∫ y in -h..h, f ((a : ℂ) + (y : ℂ) * I) * I) =
      F ((a : ℂ) + (h : ℂ) * I) - F ((a : ℂ) + (-h : ℝ) * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro y hy
  simpa using ((hd y hy).comp (y : ℂ)
    (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ))).comp_ofReal

private theorem sixRectBoundary_eq_zero_of_analytic (a b h : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (uIcc a b ×ℂ uIcc (-h) h)) :
    sixRectBoundary a b h f = 0 := by
  have ht := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (-h : ℝ) * I) ((b : ℂ) + (h : ℂ) * I)
    (by simpa using hf.differentiableOn)
  simpa only [sixRectBoundary, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add, smul_eq_mul, intervalIntegral.integral_mul_const,
    mul_comm I] using ht

private theorem log_neg_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub]; ring

private theorem log_neg_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz, ofReal_add]; ring

private theorem sixRectBoundary_simplePole (a b h c : ℝ)
    (hac : a < c) (hcb : c < b) (hh : 0 < h) :
    sixRectBoundary a b h (fun z => (z - (c : ℂ))⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hhor (y : ℝ) (hy : y ≠ 0) :
      (∫ x in a..b, (((x : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹) =
        Complex.log ((b : ℂ) + (y : ℂ) * I - c) -
          Complex.log ((a : ℂ) + (y : ℂ) * I - c) := by
    apply horizontal_primitive (fun z => Complex.log (z - c)) (fun z => (z - c)⁻¹) a b y
    · intro x _
      have hs : (x : ℂ) + (y : ℂ) * I - c ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inr (by simpa using hy))
      simpa [Function.comp_def] using! (Complex.hasDerivAt_log hs).comp ((x : ℂ) + (y : ℂ) * I)
        ((hasDerivAt_id _).sub_const (c : ℂ))
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro x
      have hz : (x : ℂ) + (y : ℂ) * I - c ≠ 0 := by
        intro he; have := congrArg Complex.im he; simp at this; exact hy this
      exact ContinuousAt.inv₀ (by fun_prop) hz
  have hvright : (∫ y in -h..h, (((b : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹ * I) =
      Complex.log ((b : ℂ) + (h : ℂ) * I - c) -
        Complex.log ((b : ℂ) + (-h : ℝ) * I - c) := by
    apply vertical_primitive (fun z => Complex.log (z - c)) (fun z => (z - c)⁻¹) b h
    · intro y _
      have hs : (b : ℂ) + (y : ℂ) * I - c ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr hcb))
      simpa [Function.comp_def] using! (Complex.hasDerivAt_log hs).comp ((b : ℂ) + (y : ℂ) * I)
        ((hasDerivAt_id _).sub_const (c : ℂ))
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro y
      apply ContinuousAt.mul _ continuousAt_const
      apply ContinuousAt.inv₀ (by fun_prop)
      intro he; have := congrArg Complex.re he; exact (sub_pos.mpr hcb).ne' (by simpa using this)
  have hvleft : (∫ y in -h..h, (((a : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹ * I) =
      Complex.log (-((a : ℂ) + (h : ℂ) * I - c)) -
        Complex.log (-((a : ℂ) + (-h : ℝ) * I - c)) := by
    apply vertical_primitive (fun z => Complex.log (-(z - c))) (fun z => (z - c)⁻¹) a h
    · intro y _
      have hs : -((a : ℂ) + (y : ℂ) * I - c) ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
      simpa only [Function.comp_def, id_eq, neg_inv, mul_neg, neg_mul, neg_neg, mul_one] using!
        (Complex.hasDerivAt_log hs).comp ((a : ℂ) + (y : ℂ) * I)
        (((hasDerivAt_id _).sub_const (c : ℂ)).neg)
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro y
      apply ContinuousAt.mul _ continuousAt_const
      apply ContinuousAt.inv₀ (by fun_prop)
      intro he; have := congrArg Complex.re he; exact (sub_neg.mpr hac).ne (by simpa using this)
  unfold sixRectBoundary
  rw [hhor (-h) (neg_ne_zero.mpr hh.ne'), hhor h hh.ne', hvright, hvleft,
    log_neg_im_pos (by simpa using hh : 0 < ((a : ℂ) + (h : ℂ) * I - c).im),
    log_neg_im_neg (by simpa using neg_neg_of_pos hh : ((a : ℂ) + (-h : ℝ) * I - c).im < 0)]
  ring

private theorem horizontal_ne_real (x y c : ℝ) (hy : y ≠ 0) :
    (x : ℂ) + (y : ℂ) * I ≠ (c : ℂ) := by
  intro he; exact hy (by simpa using congrArg Complex.im he)

private theorem vertical_ne_real (x y c : ℝ) (hx : x ≠ c) :
    (x : ℂ) + (y : ℂ) * I ≠ (c : ℂ) := by
  intro he; exact hx (by simpa using congrArg Complex.re he)

private theorem sixRectBoundary_higherPole (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    sixRectBoundary a b h (fun z => ((z - (c : ℂ)) ^ (k + 1))⁻¹) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ t : ℕ, k = t + 1 := ⟨k - 1, by omega⟩
  let F : ℂ → ℂ := fun z => -((z - (c : ℂ)) ^ (k + 1))⁻¹ / ((k + 1 : ℕ) : ℂ)
  let f : ℂ → ℂ := fun z => ((z - (c : ℂ)) ^ (k + 1 + 1))⁻¹
  have hd : ∀ z ≠ (c : ℂ), HasDerivAt F (f z) z := by
    intro z hz
    have hz0 : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
    have h1 := ((((hasDerivAt_id z).sub_const (c : ℂ)).pow (k + 1)).inv
      (pow_ne_zero (k + 1) hz0)).neg.div_const ((k + 1 : ℕ) : ℂ)
    convert! h1 using 1
    simp only [f, id_eq, Pi.pow_apply, mul_one, Nat.add_sub_cancel]
    field_simp; simp only [pow_succ]; ring
  have hc : ∀ z ≠ (c : ℂ), ContinuousAt f z := fun z hz =>
    ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hz))
  have hhori (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume a b :=
    (continuous_iff_continuousAt.mpr fun x =>
      (hc _ (horizontal_ne_real x y c hy)).comp
        (f := fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (by fun_prop)).intervalIntegrable a b
  have hvert (x : ℝ) (hx : x ≠ c) :
      IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I) * I) volume (-h) h :=
    (continuous_iff_continuousAt.mpr fun y =>
      ((hc _ (vertical_ne_real x y c hx)).comp
        (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).intervalIntegrable (-h) h
  unfold sixRectBoundary
  rw [horizontal_primitive F f a b (-h)
        (fun x _ => hd _ (horizontal_ne_real x (-h) c (neg_ne_zero.mpr hh)))
        (hhori (-h) (neg_ne_zero.mpr hh)),
      horizontal_primitive F f a b h
        (fun x _ => hd _ (horizontal_ne_real x h c hh)) (hhori h hh),
      vertical_primitive F f b h (fun y _ => hd _ (vertical_ne_real b y c hb)) (hvert b hb),
      vertical_primitive F f a h (fun y _ => hd _ (vertical_ne_real a y c ha)) (hvert a ha)]
  ring

private def sixPolePrincipal (f : ℂ → ℂ) (c z : ℂ) : ℂ :=
  sixPoleTaylorTail f c 0 c / (z - c) ^ 5 +
  sixPoleTaylorTail f c 1 c / (z - c) ^ 4 +
  sixPoleTaylorTail f c 2 c / (z - c) ^ 3 +
  sixPoleTaylorTail f c 3 c / (z - c) ^ 2 +
  sixPoleTaylorTail f c 4 c / (z - c)

private theorem taylor_step (f : ℂ → ℂ) (c z : ℂ) (k : ℕ) :
    (z - c) * sixPoleTaylorTail f c (k + 1) z =
      sixPoleTaylorTail f c k z - sixPoleTaylorTail f c k c := by
  simpa only [sixPoleTaylorTail, Function.iterate_succ_apply', Function.swap,
    smul_eq_mul] using sub_smul_dslope (sixPoleTaylorTail f c k) c z

private theorem sixPolePrincipal_exact (f : ℂ → ℂ) (c z : ℂ) (hz : z ≠ c) :
    f z / (z - c) ^ 5 = sixPolePrincipal f c z + sixPoleTaylorTail f c 5 z := by
  have h0 := taylor_step f c z 0; have h1 := taylor_step f c z 1
  have h2 := taylor_step f c z 2; have h3 := taylor_step f c z 3
  have h4 := taylor_step f c z 4
  have hz0 := sub_ne_zero.mpr hz
  unfold sixPolePrincipal
  apply (div_eq_iff (pow_ne_zero 5 hz0)).mpr
  field_simp
  change (z - c) * sixPoleTaylorTail f c 1 z = f z - f c at h0
  rw [show sixPoleTaylorTail f c 0 c = f c from rfl]
  linear_combination -h0 - (z - c) * h1 - (z - c) ^ 2 * h2 - (z - c) ^ 3 * h3 - (z - c) ^ 4 * h4

private theorem sixPolePrincipal_analyticAt (f : ℂ → ℂ) (c z : ℂ) (hz : z ≠ c) :
    AnalyticAt ℂ (sixPolePrincipal f c) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ => w - c) z := analyticAt_id.sub analyticAt_const
  have hz0 := sub_ne_zero.mpr hz
  exact ((((analyticAt_const.div (hd.pow 5) (pow_ne_zero 5 hz0)).add
    (analyticAt_const.div (hd.pow 4) (pow_ne_zero 4 hz0))).add
    (analyticAt_const.div (hd.pow 3) (pow_ne_zero 3 hz0))).add
    (analyticAt_const.div (hd.pow 2) (pow_ne_zero 2 hz0))).add
    (analyticAt_const.div hd hz0)

private structure SixRectIntegrable (a b h : ℝ) (f : ℂ → ℂ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (-h : ℝ) * I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I) * I) volume (-h) h
  left : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I) * I) volume (-h) h

private theorem sixRectIntegrable_of_edges (a b h : ℝ) (f : ℂ → ℂ)
    (hbot : ∀ x ∈ uIcc a b, ContinuousAt f ((x : ℂ) + (-h : ℝ) * I))
    (htop : ∀ x ∈ uIcc a b, ContinuousAt f ((x : ℂ) + (h : ℂ) * I))
    (hr : ∀ y ∈ uIcc (-h) h, ContinuousAt f ((b : ℂ) + (y : ℂ) * I))
    (hl : ∀ y ∈ uIcc (-h) h, ContinuousAt f ((a : ℂ) + (y : ℂ) * I)) :
    SixRectIntegrable a b h f :=
  ⟨ContinuousOn.intervalIntegrable fun x hx =>
      ((hbot x hx).comp (f := fun x : ℝ => (x : ℂ) + (-h : ℝ) * I) (by fun_prop)).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun x hx =>
      ((htop x hx).comp (f := fun x : ℝ => (x : ℂ) + (h : ℂ) * I) (by fun_prop)).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun y hy =>
      (((hr y hy).comp (f := fun y : ℝ => (b : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun y hy =>
      (((hl y hy).comp (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).continuousWithinAt⟩

private theorem SixRectIntegrable.add {a b h : ℝ} {f g : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (hg : SixRectIntegrable a b h g) :
    SixRectIntegrable a b h (fun z => f z + g z) :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top,
   by simpa only [add_mul] using hf.right.add hg.right,
   by simpa only [add_mul] using hf.left.add hg.left⟩

private theorem SixRectIntegrable.const_mul {a b h : ℝ} {f : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (c : ℂ) :
    SixRectIntegrable a b h (fun z => c * f z) :=
  ⟨hf.bottom.const_mul c, hf.top.const_mul c,
   by simpa only [mul_assoc] using hf.right.const_mul c,
   by simpa only [mul_assoc] using hf.left.const_mul c⟩

private theorem sixRectBoundary_add {a b h : ℝ} {f g : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (hg : SixRectIntegrable a b h g) :
    sixRectBoundary a b h (fun z => f z + g z) =
      sixRectBoundary a b h f + sixRectBoundary a b h g := by
  unfold sixRectBoundary
  simp only [add_mul, intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top,
    intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

private theorem sixRectBoundary_const_mul (a b h : ℝ) (f : ℂ → ℂ) (c : ℂ) :
    sixRectBoundary a b h (fun z => c * f z) = c * sixRectBoundary a b h f := by
  unfold sixRectBoundary
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

private theorem sixRectIntegrable_purePole (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (k : ℕ) :
    SixRectIntegrable a b h (fun z => ((z - (c : ℂ)) ^ k)⁻¹) := by
  have hf (z : ℂ) (hz : z ≠ c) : ContinuousAt (fun w : ℂ => ((w - c) ^ k)⁻¹) z :=
    ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero k (sub_ne_zero.mpr hz))
  exact sixRectIntegrable_of_edges a b h _
    (fun x _ => hf _ (horizontal_ne_real x (-h) c (neg_ne_zero.mpr hh)))
    (fun x _ => hf _ (horizontal_ne_real x h c hh))
    (fun y _ => hf _ (vertical_ne_real b y c hb))
    (fun y _ => hf _ (vertical_ne_real a y c ha))

private theorem sixRectIntegrable_principal (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (f : ℂ → ℂ) : SixRectIntegrable a b h (sixPolePrincipal f c) := by
  have hi (k : ℕ) := sixRectIntegrable_purePole a b h c ha hb hh k
  unfold sixPolePrincipal
  simpa only [div_eq_mul_inv, pow_one] using
    ((((hi 5).const_mul (sixPoleTaylorTail f c 0 c)).add
      ((hi 4).const_mul (sixPoleTaylorTail f c 1 c))).add
      ((hi 3).const_mul (sixPoleTaylorTail f c 2 c))).add
      ((hi 2).const_mul (sixPoleTaylorTail f c 3 c)) |>.add
      ((hi 1).const_mul (sixPoleTaylorTail f c 4 c))

private theorem sixRectBoundary_principal (a b h c : ℝ) (hac : a < c) (hcb : c < b)
    (hh : 0 < h) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f (c : ℂ)) :
    sixRectBoundary a b h (sixPolePrincipal f c) =
      (2 * (Real.pi : ℂ) * I) * (iteratedDeriv 4 f c / 24) := by
  have hi (k : ℕ) := sixRectIntegrable_purePole a b h c hac.ne hcb.ne.symm hh.ne' k
  have hc (k r : ℕ) := (hi k).const_mul (sixPoleTaylorTail f c r c)
  unfold sixPolePrincipal
  simp only [div_eq_mul_inv]
  rw [sixRectBoundary_add (((hc 5 0).add (hc 4 1)).add (hc 3 2) |>.add (hc 2 3))
      (by simpa only [pow_one] using hc 1 4),
    sixRectBoundary_add (((hc 5 0).add (hc 4 1)).add (hc 3 2)) (hc 2 3),
    sixRectBoundary_add ((hc 5 0).add (hc 4 1)) (hc 3 2),
    sixRectBoundary_add (hc 5 0) (hc 4 1)]
  simp only [sixRectBoundary_const_mul]
  rw [sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 4 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 3 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 2 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 1 (by norm_num),
    sixRectBoundary_simplePole a b h c hac hcb hh,
    sixPoleTaylorTail_at_center hf 4]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  ring

private theorem fill_finite_analytic (S : Finset ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hloc : ∀ c ∈ S, ∃ A : ℂ → ℂ, AnalyticAt ℂ A c ∧ f =ᶠ[𝓝[≠] c] A) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∉ S, G z = f z := by
  classical
  let A : ℂ → ℂ → ℂ := fun c => if hc : c ∈ S then (hloc c hc).choose else f
  have hA (c : ℂ) (hc : c ∈ S) : AnalyticAt ℂ (A c) c ∧ f =ᶠ[𝓝[≠] c] A c := by
    simpa only [A, dite_eq_left hc] using (hloc c hc).choose_spec
  let G : ℂ → ℂ := fun z => if z ∈ S then A z z else f z
  refine ⟨G, ?_, fun z hz => by simp only [G, ite_eq_right hz]⟩
  intro c hcU
  by_cases hc : c ∈ S
  · apply (hA c hc).1.congr
    have he : ∀ᶠ z in 𝓝 c, z ∉ S.erase c :=
      (S.erase c).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [he, eventually_nhdsWithin_iff.mp (hA c hc).2] with z hz hzg
    by_cases hzc : z = c
    · subst z; simp only [G, ite_eq_left hc]
    · have hzs : z ∉ S := fun hzs => hz (Finset.mem_erase.mpr ⟨hzc, hzs⟩)
      simpa only [G, ite_eq_right hzs] using (hzg hzc).symm
  · apply (hf c hcU hc).congr
    filter_upwards [S.finite_toSet.isClosed.isOpen_compl.mem_nhds hc] with z hz
    have hz' : z ∉ S := hz
    simp only [G, ite_eq_right hz']

private theorem finite_principal_removal (S : Finset ℂ) (U : Set ℂ)
    (f g : ℂ → ℂ) (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hloc : ∀ c ∈ S, ∃ A : ℂ → ℂ, AnalyticAt ℂ A c ∧
      f =ᶠ[𝓝[≠] c] (fun z => sixPolePrincipal g c z + A z)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z ∉ S, f z = G z + ∑ c ∈ S, sixPolePrincipal g c z := by
  classical
  let R : ℂ → ℂ := fun z => f z - ∑ c ∈ S, sixPolePrincipal g c z
  obtain ⟨G, hG, he⟩ := fill_finite_analytic S U R
    (fun z hz hzs => (hf z hz hzs).sub (by
      convert! S.analyticAt_sum
        (fun c hc => sixPolePrincipal_analyticAt g c z (fun he => hzs (he ▸ hc))) using 1
      funext w; simp only [Finset.sum_apply]))
    (fun c hc => by
      obtain ⟨A, hA, he⟩ := hloc c hc
      refine ⟨fun z => A z - ∑ d ∈ S.erase c, sixPolePrincipal g d z, ?_, ?_⟩
      · apply hA.sub
        convert! (S.erase c).analyticAt_sum
          (fun d hd => sixPolePrincipal_analyticAt g d c (Finset.mem_erase.mp hd).1.symm) using 1
        funext w; simp only [Finset.sum_apply]
      · filter_upwards [he] with z hz
        dsimp only [R]; rw [← Finset.add_sum_erase _ _ hc, hz]; ring)
  refine ⟨G, hG, fun z hz => ?_⟩
  have ht := he z hz; dsimp only [R] at ht; linear_combination -ht

private def rectanglePoleSet (n q : ℕ) : Finset ℂ :=
  (Finset.Icc (-(anchor n : ℤ)) (q : ℤ)).image (fun m : ℤ => (m : ℂ))

private theorem rectanglePoleSet_mem (n q : ℕ) (z : ℂ) :
    z ∈ rectanglePoleSet n q ↔
      ∃ m : ℤ, -(anchor n : ℤ) ≤ m ∧ m ≤ (q : ℤ) ∧ (m : ℂ) = z := by
  simp only [rectanglePoleSet, Finset.mem_image, Finset.mem_Icc]; aesop

/-- **Main Vertical Contour Identity**: for every `n` and `i, j < 40 n`, the complete
upward vertical line integral along `Re z = -n - 1/2` equals `-(2 π i) * kernelFunctional n i j`. -/
theorem verticalIntegral_eq_functional (n : ℕ) (i j : Fin (fiveRank n)) :
    verticalIntegral n i j =
      -(2 * (Real.pi : ℂ) * I) * (fiveFunctional n i j : ℂ) := by
  classical
  have hrect : ∀ q : ℕ, 1 ≤ q →
      clockwiseRectangleIntegral n i j q =
        -(2 * (Real.pi : ℂ) * I) *
          ∑ v ∈ Finset.range (q + anchor n + 1),
            iteratedDeriv 4 (entryComplex n i j) ((v : ℂ) - (anchor n : ℂ)) / 24 := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hab : contourAbscissa n ≤ (q : ℝ) + 1 / 2 := by
      dsimp [contourAbscissa]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hclock : clockwiseRectangleIntegral n i j q =
        -sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
          (contourIntegrand n i j) := by
      unfold clockwiseRectangleIntegral sixRectBoundary horizontalClosingIntegral
        rightClosingIntegral verticalTruncation verticalIntegrand contourPoint
      simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [hclock]
    obtain ⟨G, hG, he⟩ := finite_principal_removal (rectanglePoleSet n q)
      (Icc (contourAbscissa n) ((q : ℝ) + 1 / 2) ×ℂ Icc (-(q : ℝ)) q)
      (contourIntegrand n i j) (entryComplex n i j)
      (fun z hz hzs => by
        apply contourIntegrand_analyticAt n i j z ((contourAbscissa_in_halfplane n).trans_le hz.1.1)
        intro hs
        obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hs
        have hzm : z = (m : ℂ) := by
          apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
          simpa only [mul_comm] using hm
        have hmlo : -(anchor n : ℤ) ≤ m := by
          have hb := hz.1.1; rw [hzm] at hb
          simp only [intCast_re, contourAbscissa] at hb
          have : -(anchor n : ℝ) - 1 < (m : ℝ) := by linarith
          have : -(anchor n : ℤ) - 1 < m := by exact_mod_cast this
          omega
        have hmhi : m ≤ (q : ℤ) := by
          have hb := hz.1.2; rw [hzm] at hb; simp only [intCast_re] at hb
          have : (m : ℝ) < (q : ℝ) + 1 := by linarith
          have : m < (q : ℤ) + 1 := by exact_mod_cast this
          omega
        exact hzs ((rectanglePoleSet_mem n q z).mpr ⟨m, hmlo, hmhi, hzm.symm⟩))
      (fun c hc => by
        obtain ⟨m, hmlo, _, rfl⟩ := (rectanglePoleSet_mem n q c).mp hc
        have hm : contourAbscissa n < (m : ℝ) := by
          have : -(anchor n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
          dsimp [contourAbscissa]; linarith
        have hf : AnalyticAt ℂ (entryComplex n i j) (m : ℂ) :=
          entryComplex_analyticAt n i j _ (by
            simpa using (lt_trans (contourAbscissa_in_halfplane n) hm))
        obtain ⟨A, hA, hK⟩ := sixContourKernel_principal_part m
        refine ⟨fun z => sixPoleTaylorTail (entryComplex n i j) m 5 z +
          entryComplex n i j z * A z, (sixPoleTaylorTail_analytic hf 5).add (hf.mul hA), ?_⟩
        filter_upwards [hK, self_mem_nhdsWithin] with z hz hzm
        rw [contourIntegrand, hz, mul_add, mul_one_div, sixPolePrincipal_exact _ _ _ hzm]; ring)
    have hG' : AnalyticOnNhd ℂ G
        (uIcc (contourAbscissa n) ((q : ℝ) + 1 / 2) ×ℂ uIcc (-(q : ℝ)) q) := by
      simpa only [uIcc_of_le hab, uIcc_of_le (by linarith : -(q : ℝ) ≤ q)] using hG
    have hGint : SixRectIntegrable (contourAbscissa n) ((q : ℝ) + 1 / 2) q G :=
      sixRectIntegrable_of_edges _ _ _ _
        (fun x hx => (hG' _ (by simpa [mem_reProdIm] using And.intro hx (left_mem_uIcc : -(q : ℝ) ∈ uIcc (-(q : ℝ)) q))).continuousAt)
        (fun x hx => (hG' _ (by simpa [mem_reProdIm] using And.intro hx (right_mem_uIcc : (q : ℝ) ∈ uIcc (-(q : ℝ)) q))).continuousAt)
        (fun y hy => (hG' _ (by simpa [mem_reProdIm] using And.intro (right_mem_uIcc : (q : ℝ) + 1 / 2 ∈ uIcc (contourAbscissa n) ((q : ℝ) + 1 / 2)) hy)).continuousAt)
        (fun y hy => (hG' _ (by simpa [mem_reProdIm] using And.intro (left_mem_uIcc : contourAbscissa n ∈ uIcc (contourAbscissa n) ((q : ℝ) + 1 / 2)) hy)).continuousAt)
    have hpb : ∀ c ∈ rectanglePoleSet n q,
        c.im = 0 ∧ contourAbscissa n < c.re ∧ c.re < (q : ℝ) + 1 / 2 := by
      intro c hc
      obtain ⟨m, hmlo, hmhi, rfl⟩ := (rectanglePoleSet_mem n q c).mp hc
      have hlo : -(anchor n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
      have hhi : (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hmhi
      simp only [intCast_im, intCast_re, contourAbscissa, true_and]
      exact ⟨by linarith, by linarith⟩
    have hpi (c : ℂ) (hc : c ∈ rectanglePoleSet n q) :
        SixRectIntegrable (contourAbscissa n) ((q : ℝ) + 1 / 2) q
          (sixPolePrincipal (entryComplex n i j) c) := by
      have hb := hpb c hc
      have hec : (c.re : ℂ) = c := by apply Complex.ext <;> simp [hb.1]
      rw [← hec]
      exact sixRectIntegrable_principal _ _ _ _ hb.2.1.ne hb.2.2.ne.symm hq0.ne' _
    have hsumInt : SixRectIntegrable (contourAbscissa n) ((q : ℝ) + 1 / 2) q
        (fun z => ∑ c ∈ rectanglePoleSet n q, sixPolePrincipal (entryComplex n i j) c z) :=
      ⟨by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).bottom) using 1; funext x; simp,
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).top) using 1; funext x; simp,
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).right) using 1; funext y; simp [Finset.sum_mul],
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).left) using 1; funext y; simp [Finset.sum_mul]⟩
    have hbd_eq : sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
        (contourIntegrand n i j) =
        (2 * (Real.pi : ℂ) * I) *
          ∑ c ∈ rectanglePoleSet n q, iteratedDeriv 4 (entryComplex n i j) c / 24 := by
      have hhor (x y : ℝ) (hy : y ≠ 0) : (x : ℂ) + (y : ℂ) * I ∉ rectanglePoleSet n q := fun hc =>
        hy (by simpa using (hpb _ hc).1)
      have hver (y x : ℝ) (hx : x = contourAbscissa n ∨ x = (q : ℝ) + 1 / 2) :
          (x : ℂ) + (y : ℂ) * I ∉ rectanglePoleSet n q := fun hc => by
        have hb := (hpb _ hc).2
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] at hb
        rcases hx with rfl | rfl <;> linarith
      have hcongr : sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
          (contourIntegrand n i j) =
          sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
            (fun z => G z + ∑ c ∈ rectanglePoleSet n q,
              sixPolePrincipal (entryComplex n i j) c z) := by
        unfold sixRectBoundary
        rw [intervalIntegral.integral_congr (fun x _ => he _ (hhor x (-q) (neg_ne_zero.mpr hq0.ne'))),
            intervalIntegral.integral_congr (fun x _ => he _ (hhor x q hq0.ne')),
            intervalIntegral.integral_congr (fun y _ => congrArg (· * I) (he _ (hver y _ (Or.inr rfl)))),
            intervalIntegral.integral_congr (fun y _ => congrArg (· * I) (he _ (hver y _ (Or.inl rfl))))]
      rw [hcongr, sixRectBoundary_add hGint hsumInt,
        sixRectBoundary_eq_zero_of_analytic _ _ _ _ hG', zero_add]
      have hsum_bd : sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
          (fun z => ∑ c ∈ rectanglePoleSet n q, sixPolePrincipal (entryComplex n i j) c z) =
          ∑ c ∈ rectanglePoleSet n q,
            sixRectBoundary (contourAbscissa n) ((q : ℝ) + 1 / 2) q
              (sixPolePrincipal (entryComplex n i j) c) := by
        unfold sixRectBoundary
        simp only [Finset.sum_mul]
        rw [intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).bottom),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).top),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).right),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).left)]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hsum_bd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hb := hpb c hc
      have hec : (c.re : ℂ) = c := by apply Complex.ext <;> simp [hb.1]
      have hf := entryComplex_analyticAt n i j c
        ((contourAbscissa_in_halfplane n).trans hb.2.1)
      simpa only [hec] using sixRectBoundary_principal
        (contourAbscissa n) ((q : ℝ) + 1 / 2) q c.re hb.2.1 hb.2.2 hq0
        (entryComplex n i j) (by simpa only [hec] using hf)
    rw [hbd_eq, ← neg_mul]
    congr 1
    have hset : rectanglePoleSet n q =
        (Finset.range (q + anchor n + 1)).image (fun v : ℕ => (v : ℂ) - (anchor n : ℂ)) := by
      ext z
      rw [rectanglePoleSet_mem, Finset.mem_image]
      constructor
      · rintro ⟨m, hmlo, hmhi, rfl⟩
        have hm0 : 0 ≤ m + (anchor n : ℤ) := by omega
        refine ⟨(m + (anchor n : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
        have hv : (((m + (anchor n : ℤ)).toNat : ℕ) : ℤ) = m + (anchor n : ℤ) := Int.toNat_of_nonneg hm0
        have hvC : ((m + (anchor n : ℤ)).toNat : ℂ) = (m : ℂ) + (anchor n : ℂ) := by exact_mod_cast hv
        rw [hvC]; ring
      · rintro ⟨v, hv, rfl⟩
        have hv' := Finset.mem_range.mp hv
        exact ⟨(v : ℤ) - (anchor n : ℤ), by omega, by omega, by push_cast; rfl⟩
    rw [hset, Finset.sum_image]
    intro a _ b _ h1
    have h2 : (a : ℂ) = b := by linear_combination h1
    exact_mod_cast h2
  have hlim : Tendsto (fun q : ℕ => ∑ v ∈ Finset.range (q + anchor n + 1),
      iteratedDeriv 4 (entryComplex n i j) ((v : ℂ) - (anchor n : ℂ)) / 24)
      atTop (𝓝 (fiveFunctional n i j : ℂ)) :=
    (hasSum_contour_residue_series n i j).tendsto_sum_nat.comp
      (tendsto_atTop.mpr fun b => eventually_atTop.2 ⟨b, fun q hq => by omega⟩)
  have hr := hlim.const_mul (-(2 * (Real.pi : ℂ) * I))
  have he : (fun q : ℕ => clockwiseRectangleIntegral n i j q) =ᶠ[atTop]
      (fun q : ℕ => -(2 * (Real.pi : ℂ) * I) *
        ∑ v ∈ Finset.range (q + anchor n + 1),
          iteratedDeriv 4 (entryComplex n i j) ((v : ℂ) - (anchor n : ℂ)) / 24) :=
    (eventually_ge_atTop 1).mono hrect
  exact tendsto_nhds_unique (clockwiseRectangleIntegral_tendsto n i j) (hr.congr' he.symm)


end OddZetaSix.B40a
