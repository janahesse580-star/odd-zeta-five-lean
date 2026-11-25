import OddZetaSix.B40a.Identity.Evaluation
import OddZetaSix.SixContour

/-! Complex evaluation, half-plane analyticity, and the protected residue series of the actual B40a entry.
The analytic estimates and residue proof adapt the MIT-licensed upstream SixContour module. -/
noncomputable section
set_option autoImplicit false
namespace OddZetaSix.B40a
open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

/-- Half-integer anchor nearest the prescribed crossing at `-0.85n`. -/
def anchor (n : ℕ) : ℕ := 17*n/20

theorem anchor_le (n : ℕ) : anchor n ≤ n := by unfold anchor; omega

theorem anchor_protected (n : ℕ) : anchor n ≤ 25*n := (anchor_le n).trans (by omega)

theorem B40a_protected_fifth_power_dvd (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 25*n) :
    (X+C (k : ℚ))^5 ∣ numerator n := by
  have hd := rising_linear_factor_dvd k (25*n) hk hkn
  unfold numerator
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left hd _) _) _

/-- Complex evaluation of `R_n(z) E_i(z + c_n) E_j(z + c_n)`. -/
def entryComplex (n i j : ℕ) (z : ℂ) : ℂ :=
  aeval z (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j) /
    aeval z (kernelDenominator n)

/-- Open pole-free half-plane `{z : ℂ | -(34 n + 1) < Re z}`. -/
def complexHalfPlane (n : ℕ) : Set ℂ :=
  {z | -(34 * (n : ℝ) + 1) < z.re}

theorem isOpen_complexHalfPlane (n : ℕ) : IsOpen (complexHalfPlane n) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem six_pole_translate_complex_ne_zero (n k : ℕ) (hk : k ∈ kernelPoleSet n)
    (z : ℂ) (hz : -(34 * (n : ℝ) + 1) < z.re) : z + (k : ℂ) ≠ 0 := by
  have hp : 0 < (z + (k : ℂ)).re := by
    simpa using kernel_pole_translate_pos n k hk z.re hz
  intro h
  simp [h] at hp

theorem six_denominator_complex_eval_ne_zero (n : ℕ) (z : ℂ)
    (hz : -(34 * (n : ℝ) + 1) < z.re) : aeval z (kernelDenominator n) ≠ 0 := by
  rw [kernel_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast]
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    pow_ne_zero _ (six_pole_translate_complex_ne_zero n k hk z hz)

theorem entryComplex_analyticAt (n i j : ℕ) (z : ℂ)
    (hz : -(34 * (n : ℝ) + 1) < z.re) : AnalyticAt ℂ (entryComplex n i j) z :=
  (analyticAt_id.aeval_polynomial
    (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j)).div
    (analyticAt_id.aeval_polynomial (kernelDenominator n))
    (six_denominator_complex_eval_ne_zero n z hz)

private theorem aeval_complex_ofReal (P : ℚ[X]) (x : ℝ) :
    aeval (x : ℂ) P = ((aeval x P : ℝ) : ℂ) :=
  aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℚ) x P

theorem entryComplex_ofReal (n i j : ℕ) (x : ℝ) :
    entryComplex n i j (x : ℂ) = (kernelEntryReal n i j x : ℂ) := by
  simp only [entryComplex, kernelEntryReal, aeval_complex_ofReal, Complex.ofReal_div]

theorem kernelPoleComplement_complex_eval (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) (z : ℂ) (hz : -(34 * (n : ℝ) + 1) < z.re) :
    aeval z (kernelPoleComplement n k l) =
      aeval z (kernelDenominator n) / (z + (k : ℂ)) ^ (l + 1) := by
  have h := congrArg (fun P : ℚ[X] => aeval z P) (kernelPoleComplement_mul n k l hk hl)
  simp only [map_mul, map_pow, map_add, aeval_X, map_natCast] at h
  exact (eq_div_iff (pow_ne_zero _ (six_pole_translate_complex_ne_zero n k hk z hz))).mpr
    (by simpa only [mul_comm] using h)

theorem entryComplex_partial_fractions (n : ℕ) (i j : Fin (fiveRank n))
    (z : ℂ) (hz : -(34 * (n : ℝ) + 1) < z.re) :
    entryComplex n i j z = ∑ k ∈ kernelPoleSet n, ∑ l,
      (kernelPrincipalCoefficients n i j k l : ℂ) / (z + (k : ℂ)) ^ (l.val + 1) := by
  unfold entryComplex
  rw [kernel_cleared_partial_fractions]
  simp only [map_sum, map_mul, aeval_C, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [kernelPoleComplement_complex_eval n k l.val hk l.isLt z hz]
  have hd := six_denominator_complex_eval_ne_zero n z hz
  have hp := pow_ne_zero (l.val + 1) (six_pole_translate_complex_ne_zero n k hk z hz)
  field_simp
  simp

theorem entryComplex_eventuallyEq_partial_fractions (n : ℕ) (i j : Fin (fiveRank n))
    (z : ℂ) (hz : -(34 * (n : ℝ) + 1) < z.re) :
    entryComplex n i j =ᶠ[𝓝 z]
      (fun w : ℂ => ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℂ) / (w + (k : ℂ)) ^ (l.val + 1)) := by
  filter_upwards [(isOpen_complexHalfPlane n).mem_nhds hz] with w hw
  exact entryComplex_partial_fractions n i j w hw

private theorem complex_iteratedDeriv_shifted_zpow (r : ℕ) (m : ℤ) (z a : ℂ) :
    iteratedDeriv r (fun w : ℂ => (w + a) ^ m) z =
      (∏ s ∈ range r, ((m : ℂ) - (s : ℂ))) * (z + a) ^ (m - (r : ℤ)) := by
  rw [iteratedDeriv_comp_add_const r (fun w : ℂ => w ^ m) a, iteratedDeriv_eq_iterate]
  exact iter_deriv_zpow m (z + a) r

private theorem complex_fourthDerivative_inv_pow_add (m : ℕ) (hm : 1 ≤ m)
    (z a : ℂ) (hz : z + a ≠ 0) :
    iteratedDeriv 4 (fun w : ℂ => 1 / (w + a) ^ m) z / 24 =
      ((m + 3).choose 4 : ℂ) / (z + a) ^ (m + 4) := by
  have hfun : (fun w : ℂ => 1 / (w + a) ^ m) =
      (fun w : ℂ => (w + a) ^ (-(m : ℤ))) := by
    funext w; simp [zpow_neg, one_div]
  rw [hfun, complex_iteratedDeriv_shifted_zpow]
  have hexp : -(m : ℤ) - (4 : ℕ) = -((m + 4 : ℕ) : ℤ) := by push_cast; ring
  rw [hexp, zpow_neg, zpow_natCast]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (fourthDerivative_coefficient m hm)
  push_cast at hc
  norm_num [Finset.prod_range_succ]
  field_simp [pow_ne_zero (m + 4) hz]
  linear_combination -hc

private theorem complex_fourthDerivative_const_div_pow_add (m : ℕ) (hm : 1 ≤ m)
    (c z a : ℂ) (hz : z + a ≠ 0) :
    iteratedDeriv 4 (fun w : ℂ => c / (w + a) ^ m) z / 24 =
      c * ((m + 3).choose 4 : ℂ) / (z + a) ^ (m + 4) := by
  have hfun : (fun w : ℂ => c / (w + a) ^ m) =
      (fun w : ℂ => c * (1 / (w + a) ^ m)) := by funext w; ring
  rw [hfun, iteratedDeriv_const_mul_field, mul_div_assoc,
    complex_fourthDerivative_inv_pow_add m hm z a hz]
  ring

private theorem complex_contDiffAt_const_div_pow_add (r m : ℕ) (c z a : ℂ)
    (hz : z + a ≠ 0) : ContDiffAt ℂ r (fun w : ℂ => c / (w + a) ^ m) z :=
  contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow m) (pow_ne_zero m hz)

theorem entryComplex_fourthDerivative (n : ℕ) (i j : Fin (fiveRank n))
    (z : ℂ) (hz : -(34 * (n : ℝ) + 1) < z.re) :
    iteratedDeriv 4 (entryComplex n i j) z / 24 =
      ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℂ) * ((l.val + 4).choose 4 : ℂ) /
          (z + (k : ℂ)) ^ (l.val + 5) := by
  have hsmooth (k : ℕ) (hk : k ∈ kernelPoleSet n) :
      ContDiffAt ℂ 4 (fun w : ℂ => ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℂ) / (w + (k : ℂ)) ^ (l.val + 1)) z := by
    apply ContDiffAt.sum
    intro l _
    exact complex_contDiffAt_const_div_pow_add 4 (l.val + 1)
      (kernelPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)
  rw [Filter.EventuallyEq.iteratedDeriv_eq 4
    (entryComplex_eventuallyEq_partial_fractions n i j z hz)]
  rw [iteratedDeriv_fun_sum hsmooth, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_fun_sum (fun l _ =>
    complex_contDiffAt_const_div_pow_add 4 (l.val + 1)
      (kernelPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    complex_fourthDerivative_const_div_pow_add (l.val + 1) (by omega)
      (kernelPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)

theorem entryComplex_dividedFourthDerivative_ofReal (n : ℕ) (i j : Fin (fiveRank n))
    (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) :
    iteratedDeriv 4 (entryComplex n i j) (x : ℂ) / 24 =
      ((iteratedDeriv 4 (kernelEntryReal n i j) x / 24 : ℝ) : ℂ) := by
  rw [entryComplex_fourthDerivative n i j (x : ℂ) (by simpa using hx),
    kernelEntryReal_fourthDerivative n i j x hx]
  push_cast
  rfl

/-- Successive analytic divided differences at a point `c`. -/
def sixPoleTaylorTail (f : ℂ → ℂ) (c : ℂ) (k : ℕ) : ℂ → ℂ :=
  (Function.swap dslope c)^[k] f

theorem sixPoleTaylorTail_analytic {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (k : ℕ) : AnalyticAt ℂ (sixPoleTaylorTail f c k) c := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_iterate_dslope_fslope k⟩

theorem sixPoleTaylorTail_at_center {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (k : ℕ) :
    sixPoleTaylorTail f c k c = iteratedDeriv k f c / k.factorial := by
  have hh := (hf.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
  rw [← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add, FormalMultilinearSeries.coeff_ofScalars] at hh
  exact hh.symm

private theorem dslope_sub_mul (c : ℂ) (g : ℂ → ℂ) (hg : ContinuousAt g c) :
    dslope (fun z => (z - c) * g z) c = g := by
  funext z
  by_cases hz : z = c
  · subst z
    rw [dslope_same]
    have hd : HasDerivAt (fun w => (w - c) * g w) (g c) c := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have hev : (fun t : ℂ => t⁻¹ • (((c + t - c) * g (c + t)) - ((c - c) * g c))) =ᶠ[𝓝[≠] 0]
          (fun t : ℂ => g (c + t)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [smul_eq_mul, add_sub_cancel_left, sub_self, zero_mul, sub_zero]
        rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]
      have hlim : Tendsto (fun t : ℂ => g (c + t)) (𝓝[≠] 0) (𝓝 (g c)) := by
        have hcont : Tendsto (fun t : ℂ => c + t) (𝓝 0) (𝓝 c) := by
          have hc : Continuous (fun t : ℂ => c + t) := by fun_prop
          have h := hc.tendsto (0 : ℂ)
          rwa [add_zero] at h
        exact (hg.tendsto.comp hcont).mono_left nhdsWithin_le_nhds
      exact hlim.congr' hev.symm
    exact hd.deriv
  · rw [dslope_of_ne _ hz, slope_def_field]
    simp only [sub_self, zero_mul, sub_zero]
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz)]

private theorem sixPoleTaylorTail_pow_mul (c : ℂ) (m : ℕ) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h c) :
    sixPoleTaylorTail (fun z => (z - c) ^ (m + 1) * h z) c m =
      fun z => (z - c) * h z := by
  induction m generalizing h with
  | zero => simp [sixPoleTaylorTail]
  | succ m ih =>
    change sixPoleTaylorTail (dslope (fun z => (z - c) ^ (m + 2) * h z) c) c m = _
    have hrew : (fun z => (z - c) ^ (m + 2) * h z) =
        (fun z => (z - c) * ((z - c) ^ (m + 1) * h z)) := by
      funext z; ring
    have hcont : ContinuousAt (fun z => (z - c) ^ (m + 1) * h z) c :=
      (((analyticAt_id.sub analyticAt_const).pow (m + 1)).mul hh).continuousAt
    rw [hrew, dslope_sub_mul c (fun z => (z - c) ^ (m + 1) * h z) hcont]
    exact ih h hh

/-- Complex fourth derivative vanishes at every protected integer `-40 n, ..., -1`. -/
theorem entryComplex_dividedFourthDerivative_protected (n : ℕ) (i j : Fin (fiveRank n))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 25 * n) :
    iteratedDeriv 4 (entryComplex n i j) (-(k : ℂ)) / 24 = 0 := by
  obtain ⟨Q, hQ⟩ := B40a_protected_fifth_power_dvd n k hk hkn
  have hhp : -(34 * (n : ℝ) + 1) < (-(k : ℂ)).re := by
    simp only [neg_re, natCast_re]
    have hkR : (k : ℝ) ≤ 25 * (n : ℝ) := by exact_mod_cast hkn
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  change kernelNumerator n = _ at hQ
  let h : ℂ → ℂ := fun z =>
    aeval z (C (kernelNormalization n) * Q * kernelCenteredMultiplier n i j) /
      aeval z (kernelDenominator n)
  have hh : AnalyticAt ℂ h (-(k : ℂ)) :=
    (analyticAt_id.aeval_polynomial _).div
      (analyticAt_id.aeval_polynomial _)
      (six_denominator_complex_eval_ne_zero n (-(k : ℂ)) hhp)
  have hEq : entryComplex n i j = fun z => (z - (-(k : ℂ))) ^ 5 * h z := by
    funext z
    simp only [entryComplex, h, hQ, map_mul, map_pow, map_add, aeval_X, aeval_C, sub_neg_eq_add]
    have hrat : (algebraMap ℚ ℂ) (k : ℚ) = (k : ℂ) := by simp
    rw [hrat]
    ring
  have hf : AnalyticAt ℂ (entryComplex n i j) (-(k : ℂ)) :=
    entryComplex_analyticAt n i j (-(k : ℂ)) hhp
  have ht := sixPoleTaylorTail_at_center hf 4
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at ht
  rw [← ht, hEq, sixPoleTaylorTail_pow_mul (-(k : ℂ)) 4 h hh]
  simp

/-- Removing the protected negative integer terms to the left of the anchor. -/
theorem hasSum_contour_residue_series (n : ℕ) (i j : Fin (fiveRank n)) :
    HasSum (fun v : ℕ => iteratedDeriv 4 (entryComplex n i j) ((v : ℂ) - (anchor n : ℂ)) / 24)
      (fiveFunctional n i j : ℂ) := by
  have horig : HasSum (fun v : ℕ =>
      iteratedDeriv 4 (entryComplex n i j) ((v : ℂ) - 25*(n : ℂ)) / 24)
      (kernelFunctional n i j : ℂ) := by
    have hreal : HasSum (fun v : ℕ =>
        iteratedDeriv 4 (kernelEntryReal n i j) ((v : ℝ) - 25*(n : ℝ)) / 24)
        (kernelFunctional n i j) := (summable_kernel_fourthDerivative n i j).hasSum
    apply (Complex.hasSum_ofReal.mpr hreal).congr_fun
    intro v
    simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using
      entryComplex_dividedFourthDerivative_ofReal n i j
        ((v : ℝ)-25*(n : ℝ)) (kernel_summation_point_in_halfline n v)
  let N := 25*n-anchor n
  have hN : N+anchor n=25*n := Nat.sub_add_cancel (anchor_protected n)
  have hshift := (hasSum_nat_add_iff' N (f := fun v : ℕ =>
      iteratedDeriv 4 (entryComplex n i j) ((v : ℂ)-25*(n : ℂ)) / 24)).mpr horig
  have hzero : (∑ v ∈ range N,
      iteratedDeriv 4 (entryComplex n i j) ((v : ℂ)-25*(n : ℂ)) / 24) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hv' := mem_range.mp hv
    have hx : (v : ℂ)-25*(n : ℂ) = -((25*n-v : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega : v ≤ 25*n)]; push_cast; ring
    rw [hx]
    exact entryComplex_dividedFourthDerivative_protected n i j (25*n-v) (by omega) (by omega)
  rw [hzero,sub_zero,← fiveFunctional_eq_kernel] at hshift
  refine hshift.congr_fun ?_
  intro v
  have hC : (N : ℂ)+(anchor n : ℂ)=25*(n : ℂ) := by exact_mod_cast hN
  have hz : ((v+N : ℕ) : ℂ)-25*(n : ℂ) = (v : ℂ)-(anchor n : ℂ) := by
    push_cast
    linear_combination hC
  rw [hz]

end OddZetaSix.B40a
