import OddZetaSix.B40a.Identity.Basis
import OddZetaSix.SixContour

/-! Exact quadratic rate of the scaled even-basis normalization.
The Stirling estimates adapt the MIT-licensed upstream SixContour module. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

private theorem normalizer_nonneg (n : ℕ) : 0 ≤ normalizer n := by unfold normalizer; positivity

/-- Basis normalization product `∏_{i < 40 n} ((evenBasis i).leadingCoeff)^2 * (50 n)^(4i)`. -/
def basisNormalization (n : ℕ) : ℝ :=
  ∏ i : Fin (fiveRank n), ((evenBasis i.val).leadingCoeff : ℝ) ^ 2 * (50 * (n : ℝ)) ^ (4 * i.val)

theorem basisNormalization_pos (n : ℕ) (hn : 0 < n) : 0 < basisNormalization n := by
  apply Finset.prod_pos
  intro i _
  have he : (0 : ℝ) < (evenBasis i.val).leadingCoeff := by exact_mod_cast evenBasis_leadingCoeff_pos i.val
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

private def factorialLogError (m : ℕ) : ℝ :=
  Real.log (m.factorial : ℝ) - ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ))

private theorem factorialLogError_bounds (m : ℕ) :
    0 ≤ factorialLogError m ∧ factorialLogError m ≤ 1 + Real.log (m : ℝ) := by
  rcases m with _ | m
  · norm_num [factorialLogError]
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by norm_num
  have hl := Stirling.le_log_factorial_stirling (Nat.succ_ne_zero m)
  have hlog := Real.log_nonneg hm1
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hu := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  dsimp only [Function.comp_def, Nat.succ_eq_add_one] at hu
  have hs : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
      Real.log_exp, Real.log_sqrt (by positivity)]
  rw [hs] at hu
  have hf := Stirling.log_stirlingSeq_formula (m + 1)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm.ne',
    Real.log_div hm.ne' (Real.exp_ne_zero 1), Real.log_exp] at hf
  dsimp only [factorialLogError]
  constructor <;> linarith

private def weightedLogSum (m : ℕ) : ℝ :=
  ∑ i ∈ range m, (i : ℝ) * Real.log (i : ℝ)

private def weightedLogIntegral (x : ℝ) : ℝ :=
  x ^ 2 / 2 * Real.log x - x ^ 2 / 4 + 1 / 4

private theorem weightedLog_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x : ℝ in 1..(m : ℝ), x * Real.log x) = weightedLogIntegral (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd (x : ℝ) (hx : x ∈ uIcc (1 : ℝ) (m : ℝ)) :
      HasDerivAt (fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4) (x * Real.log x) x := by
    rw [uIcc_of_le hmR] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := ((((hasDerivAt_id x).pow 2).div_const 2).mul
      (Real.hasDerivAt_log hx0)).sub (((hasDerivAt_id x).pow 2).div_const 4)
    convert! h using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply]
    field_simp; ring
  simpa [weightedLogIntegral] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Real.continuous_mul_log.intervalIntegrable _ _)

private theorem weightedLogSum_bounds (m : ℕ) (hm : 1 ≤ m) :
    weightedLogIntegral (m : ℝ) - (m : ℝ) * Real.log (m : ℝ) ≤ weightedLogSum m ∧
      weightedLogSum m ≤ weightedLogIntegral (m : ℝ) := by
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Icc (1 : ℝ) (m : ℝ)) := by
    intro x hx y hy hxy
    exact mul_le_mul hxy (Real.log_le_log (by linarith [hx.1]) hxy)
      (Real.log_nonneg hx.1) (by linarith [hy.1])
  have hmono' : MonotoneOn (fun x : ℝ => x * Real.log x) (Icc (↑(1 : ℕ)) (m : ℝ)) := by
    simpa only [Nat.cast_one] using hmono
  have hl := hmono'.sum_le_integral_Ico hm
  have hu := hmono'.integral_le_sum_Ico hm
  norm_num only [Nat.cast_one] at hl hu
  rw [weightedLog_integral m hm, Finset.sum_Ico_eq_sub _ hm] at hl hu
  simp only [sum_range_one, Nat.cast_zero, Real.log_zero, sub_zero, mul_zero,
    Nat.zero_add, Nat.cast_one, Real.log_one] at hl hu
  have hshift : (∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)) =
      weightedLogSum m + (m : ℝ) * Real.log (m : ℝ) := by
    have h := Finset.sum_range_succ' (fun i : ℕ => (i : ℝ) * Real.log (i : ℝ)) m
    rw [Finset.sum_range_succ] at h
    simpa [weightedLogSum] using h.symm
  rw [hshift] at hu
  exact ⟨by linarith, hl⟩

private theorem sum_natCast (m : ℕ) :
    (∑ i ∈ range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem leadingCoeff_log (i : ℕ) :
    Real.log ((evenBasis i).leadingCoeff : ℝ) =
      Real.log 2 - Real.log ((2 * i).factorial : ℝ) - (if i = 0 then Real.log 2 else 0) := by
  cases i with
  | zero => simp
  | succ i =>
    rw [evenBasis_leadingCoeff_succ]; push_cast
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]; simp

/-- Exact quadratic normalization rate limit `θ(3 - 2 log(2θ))` at `θ = 4/5`. -/
theorem basisNormalization_log_rate :
    Tendsto (fun n : ℕ => Real.log (basisNormalization n) / normalizer n)
      atTop (𝓝 ((12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8))) := by
  let main (n : ℕ) : ℝ :=
    (4800 + 3200 * Real.log (5 / 8)) * (n : ℝ) ^ 2 -
      80 * (n : ℝ) * Real.log (25 * (n : ℝ)) - 80 * (n : ℝ) - 1 + (80 * (n : ℝ) - 2) * Real.log 2
  have hbounds : ∀ n : ℕ, 1 ≤ n →
      main n - 80 * (n : ℝ) * (1 + Real.log (80 * (n : ℝ))) ≤
          Real.log (basisNormalization n) ∧
        Real.log (basisNormalization n) ≤
          main n + 160 * (n : ℝ) * Real.log (40 * (n : ℝ)) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h50n : (0 : ℝ) < 50 * n := by positivity
    have he (i : ℕ) : (0 : ℝ) < (evenBasis i).leadingCoeff := by
      exact_mod_cast evenBasis_leadingCoeff_pos i
    have hlog_sum : Real.log (basisNormalization n) =
        (80 * (n : ℝ) - 2) * Real.log 2 -
          2 * (∑ i ∈ range (40 * n), Real.log ((2 * i).factorial : ℝ)) +
          80 * (n : ℝ) * (40 * (n : ℝ) - 1) * Real.log (50 * (n : ℝ)) := by
      rw [basisNormalization, Real.log_prod (fun i _ =>
        mul_ne_zero (pow_ne_zero 2 (he i.val).ne') (pow_ne_zero _ h50n.ne'))]
      have hrow (i : ℕ) :
          Real.log (((evenBasis i).leadingCoeff : ℝ) ^ 2 * (50 * (n : ℝ)) ^ (4 * i)) =
            2 * Real.log ((evenBasis i).leadingCoeff : ℝ) + (4 * Real.log (50 * (n : ℝ))) * (i : ℝ) := by
        rw [Real.log_mul (pow_ne_zero 2 (he i).ne') (pow_ne_zero _ h50n.ne'),
          Real.log_pow, Real.log_pow]; push_cast; ring
      simp_rw [hrow]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        2 * Real.log ((evenBasis i).leadingCoeff : ℝ) + (4 * Real.log (50 * (n : ℝ))) * (i : ℝ)) (fiveRank n)]
      unfold fiveRank
      simp_rw [leadingCoeff_log]
      have hif : (∑ i ∈ range (40 * n), if i = 0 then Real.log 2 else 0) = Real.log 2 := by
        simp [show 0 < 40 * n by omega]
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hif, sum_natCast]
      push_cast; ring
    let fErr : ℝ := ∑ i ∈ range (40 * n), factorialLogError (2 * i)
    have hfErr_bnds : 0 ≤ fErr ∧ fErr ≤ 40 * (n : ℝ) * (1 + Real.log (80 * (n : ℝ))) := by
      constructor
      · exact Finset.sum_nonneg fun i _ => (factorialLogError_bounds (2 * i)).1
      · calc
          fErr ≤ ∑ _i ∈ range (40 * n), (1 + Real.log (80 * (n : ℝ))) := by
            apply Finset.sum_le_sum; intro i hi
            by_cases hi0 : i = 0
            · subst i
              simp only [Nat.mul_zero, factorialLogError, Nat.factorial_zero, Nat.cast_one,
                Real.log_one, Nat.cast_zero, Real.log_zero, zero_mul, sub_zero]
              have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
              linarith [Real.log_nonneg (show (1 : ℝ) ≤ 80 * (n : ℝ) by linarith)]
            · have hip : (0 : ℝ) < (2 * i : ℕ) := by
                exact_mod_cast Nat.mul_pos (by omega : 0 < 2) (Nat.pos_of_ne_zero hi0)
              have hiR : (i : ℝ) < 40 * (n : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
              have hlog := Real.log_le_log hip (show ((2 * i : ℕ) : ℝ) ≤ 80 * (n : ℝ) by
                push_cast; linarith)
              linarith [(factorialLogError_bounds (2 * i)).2]
          _ = _ := by simp; ring
    have hdecomp : Real.log (basisNormalization n) =
        main n + 4 * (weightedLogIntegral (40 * (n : ℝ)) - weightedLogSum (40 * n)) - 2 * fErr := by
      have hterm (i : ℕ) : Real.log ((2 * i).factorial : ℝ) =
          (2 * Real.log 2) * (i : ℝ) + 2 * ((i : ℝ) * Real.log (i : ℝ)) - 2 * (i : ℝ) +
            factorialLogError (2 * i) := by
        rcases eq_or_ne i 0 with rfl | hi
        · simp [factorialLogError]
        · unfold factorialLogError
          rw [Nat.cast_mul, Nat.cast_ofNat,
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hi)]
          ring
      have hlog50 : Real.log (50 * (n : ℝ)) = Real.log 2 + Real.log (25 * (n : ℝ)) := by
        rw [show 50 * (n : ℝ) = 2 * (25 * (n : ℝ)) by ring,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      have hlog_ratio : Real.log (25 * (n : ℝ)) - Real.log (40 * (n : ℝ)) = Real.log (5 / 8) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp; ring
      rw [hlog_sum]
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_natCast]
      change (80 * (n : ℝ) - 2) * Real.log 2 -
          2 * (2 * Real.log 2 * ((40 * n : ℕ) * ((40 * n : ℕ) - 1) / 2) +
            2 * weightedLogSum (40 * n) - 2 * ((40 * n : ℕ) * ((40 * n : ℕ) - 1) / 2) + fErr) +
          80 * (n : ℝ) * (40 * (n : ℝ) - 1) * Real.log (50 * (n : ℝ)) = _
      dsimp only [main, weightedLogIntegral]
      rw [hlog50]
      push_cast
      linear_combination 3200 * (n : ℝ) ^ 2 * hlog_ratio
    have hws := weightedLogSum_bounds (40 * n) (by omega)
    push_cast at hws
    constructor <;> linarith
  have hlog_div : ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun n : ℕ => Real.log (c * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    intro c hc
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using!
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add h1
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.log_mul hc (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), add_div]
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hmain_lim : Tendsto (fun n : ℕ => main n / normalizer n)
      atTop (𝓝 ((12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8))) := by
    have hc : Tendsto (fun _ : ℕ => (12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8))
        atTop (𝓝 ((12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8))) := tendsto_const_nhds
    have h := (((hc.sub ((hlog_div 25 (by norm_num)).const_mul (80 / 2000))).sub
      (hi.const_mul (80 / 2000))).sub ((hi.pow 2).const_mul (1 / 2000))).add
      (((hi.const_mul (80 / 2000)).sub ((hi.pow 2).const_mul (2 / 2000))).mul_const (Real.log 2))
    norm_num only [mul_zero, sub_zero, zero_pow, zero_sub, zero_mul, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [normalizer]; dsimp only [main]; field_simp; ring
  have hlo_err : Tendsto (fun n : ℕ => 80 * (n : ℝ) * (1 + Real.log (80 * (n : ℝ))) / normalizer n)
      atTop (𝓝 0) := by
    have h := (hi.add (hlog_div 80 (by norm_num))).const_mul (80 / 2000)
    simp only [add_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [normalizer]; field_simp
  have hhi_err : Tendsto (fun n : ℕ => 160 * (n : ℝ) * Real.log (40 * (n : ℝ)) / normalizer n)
      atTop (𝓝 0) := by
    have h := (hlog_div 40 (by norm_num)).const_mul (160 / 2000)
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [normalizer]; field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hmain_lim.sub hlo_err)
    (by simpa only [add_zero] using hmain_lim.add hhi_err)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [sub_div] using div_le_div_of_nonneg_right (hbounds n hn).1 (normalizer_nonneg n)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [add_div] using div_le_div_of_nonneg_right (hbounds n hn).2 (normalizer_nonneg n)

theorem basisNormalization_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      basisNormalization n ≤
        Real.exp (((12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8) + ε) * normalizer n) := by
  have hu := basisNormalization_log_rate.eventually_lt_const
    (show (12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8) <
      (12 : ℝ) / 5 + 8 / 5 * Real.log (5 / 8) + ε by linarith)
  filter_upwards [hu, eventually_gt_atTop (0 : ℕ)] with n hup hn
  have hnorm_pos : 0 < normalizer n := by
    rw [normalizer]; have : (0 : ℝ) < n := Nat.cast_pos.mpr hn; positivity
  exact Real.le_exp_of_log_le ((div_lt_iff₀ hnorm_pos).mp hup).le

/-- Stirling bounds also used for individual finite contour blocks. -/
theorem block_factorial_log (m : ℕ) :
    m*Real.log (m:ℝ)-m ≤ Real.log (m.factorial:ℝ) ∧
    Real.log (m.factorial:ℝ) ≤ m*Real.log (m:ℝ)-m+1+Real.log (m:ℝ) := by
  have ⟨h1,h2⟩ := factorialLogError_bounds m
  unfold factorialLogError at h1 h2
  constructor <;> linarith only [h1,h2]

end OddZetaSix.B40a
