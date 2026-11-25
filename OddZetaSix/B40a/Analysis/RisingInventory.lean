import OddZetaSix.B40a.Analysis.FiniteBlockRate
import OddZetaSix.B40a.Analysis.BentKernelDecay
noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Finset Polynomial

def riseRatio (m : ℕ) (q : ℚ) (z : ℂ) := ‖aeval z (rising q m)‖/(m.factorial:ℝ)
def poleRatio (m : ℕ) (q : ℚ) (z : ℂ) := (m.factorial:ℝ)/‖aeval z (rising q (m+1))‖

theorem rise_eq (m : ℕ) (q : ℚ) (z : ℂ) (D a y θ : ℝ) (hD : 0<D)
    (hr : z.re+(q:ℝ)=D*(a+θ)) (hi : |z.im|=D*y) :
    riseRatio m q z=normalizedBlock m D a y θ := by
  unfold riseRatio normalizedBlock; rw [rising_eq_sampled m q z D a y θ hD hr hi]; ring

theorem pole_le (m : ℕ) (q : ℚ) (z : ℂ) (D a y θ : ℝ) (hD : 0<D)
    (hr : z.re+(q:ℝ)=D*(a+θ)) (hi : |z.im|=D*y) (hbound : 1≤z.re+(q:ℝ)+m) :
    poleRatio m q z ≤ (normalizedBlock m D a y θ)⁻¹ := by
  have H : 1≤‖z+((q:ℂ)+(m:ℂ))‖ := hbound.trans (by simpa [Complex.add_re,add_assoc] using Complex.re_le_norm (z+((q:ℂ)+m)))
  have he : rising q (m+1)=rising q m*(X+C (q+(m:ℚ))) := by unfold rising; rw [Finset.prod_range_succ]
  rw [←rise_eq m q z D a y θ hD hr hi]
  unfold poleRatio riseRatio
  rw [he,map_mul,norm_mul,map_add,aeval_X,aeval_C,map_add,map_natCast]
  have bound : ‖z+((q:ℂ)+(m:ℂ))‖⁻¹≤1 := inv_le_one_of_one_le₀ H
  calc
    _ = ((m.factorial:ℝ)/‖aeval z (rising q m)‖)*‖z+((q:ℂ)+m)‖⁻¹ := by simp [div_eq_mul_inv]; ring
    _ ≤ ((m.factorial:ℝ)/‖aeval z (rising q m)‖)*1 :=
      mul_le_mul_of_nonneg_left bound (by positivity)
    _ = _ := by simp

theorem rise_nonneg (m : ℕ) (q : ℚ) (z : ℂ) : 0≤riseRatio m q z := by unfold riseRatio; positivity
theorem pole_nonneg (m : ℕ) (q : ℚ) (z : ℂ) : 0≤poleRatio m q z := by unfold poleRatio; positivity

/-- Regroup the actual twelve factors by their three offsets. -/
theorem base_norm_inventory (n : ℕ) (z : ℂ) :
    ‖entryComplex n 0 0 z‖ =
      2*‖z+(OddZetaSix.B40a.center n:ℂ)‖*
      (riseRatio (25*n) 1 z*riseRatio (25*n) (93*(n:ℚ)+2) z)^5*
      poleRatio (50*n) (34*(n:ℚ)+1) z^6*poleRatio (34*n) (42*(n:ℚ)+1) z^4*
      poleRatio (32*n) (43*(n:ℚ)+1) z^2 := by
  have numN : 0≤(normalization n:ℝ) := by unfold normalization; positivity
  simp only [entryComplex,kernelCenteredMultiplier,evenBasis_zero,one_comp,map_mul,
    aeval_C,mul_one,norm_div,norm_mul]
  have hN : ‖(algebraMap ℚ ℂ) (normalization n)‖=(normalization n:ℝ) := by
    change ‖((normalization n:ℝ):ℂ)‖=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg numN]
  rw [hN]
  simp only [kernelNumerator,numerator,kernelDenominator,denominator,map_prod,map_mul,map_natCast,
    map_pow,map_add,aeval_X,Complex.norm_prod,norm_mul,norm_pow]
  unfold riseRatio poleRatio normalization
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,offsets,Matrix.cons_val_zero,Matrix.cons_val_succ,mul_one]
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    map_add,map_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]; ring
end OddZetaSix.B40a.Cert
