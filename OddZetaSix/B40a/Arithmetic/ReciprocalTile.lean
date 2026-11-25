import OddZetaSix.SixPeriodicRate
import OddZetaSix.B40a.Arithmetic.SmallTileBound
import OddZetaSix.B40a.Arithmetic.AffineMean
import OddZetaSix.B40a.Arithmetic.SmallMidpointAudit

noncomputable section
namespace OddZetaSix.B40a.Cert.PeriodAffine
open MeasureTheory Set

private theorem continuous_realVal (L : Line) : Continuous (realVal L) := by
  unfold realVal; fun_prop

theorem smallTileWeight_continuous (r : ArithRow) (k : ℕ) (a b : ℝ) (ha : 0<a) :
    ContinuousOn (smallTileWeight r k) (Icc a b) := by
  intro x hx
  have hn : x ≠ 0 := (ha.trans_le hx.1).ne'
  unfold smallTileWeight linearProfile squareProfile realVal
  fun_prop (disch := assumption)

private theorem profiles_nonneg (r : ArithRow) (ok : check r = true) {t : ℝ}
    (ht : t ∈ Icc (r.left:ℝ) r.right) : 0 ≤ linearProfile r t ∧ 0 ≤ squareProfile r t := by
  have h : r.left < r.right := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1
  have hR : (r.left:ℝ)<r.right := by exact_mod_cast h
  have hc : IsClosed {x : ℝ | 0≤linearProfile r x ∧ 0≤squareProfile r x} :=
    (isClosed_le continuous_const (continuous_realVal _)).inter
      (isClosed_le continuous_const (continuous_realVal _))
  have hs : Ioo (r.left:ℝ) (r.right:ℝ) ⊆ {x : ℝ | 0≤linearProfile r x ∧ 0≤squareProfile r x} := by
    intro x hx
    constructor
    · rw [linearProfile,← period_integral_affine r ok _ hx]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
        dsimp [linearTerm]; exact_mod_cast (periodicScore_bounds x u).1)
    · rw [squareProfile,← period_integral_affine r ok _ hx]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
        dsimp [squareTerm]; exact_mod_cast Int.ediv_nonneg (sq_nonneg _) (by decide : (0:ℤ) ≤ 4))
  apply closure_minimal hs hc
  rwa [closure_Ioo hR.ne]

/-- Integral on one reciprocal tile is bounded using the left-endpoint
Jacobian and the two exact affine mean values of the certificate. -/
theorem reciprocal_tile_integral (r : ArithRow) (hr : r ∈ smallRows) (ok : check r = true)
    (k : ℕ) (hpos : 0<(k:ℝ)+r.left) :
    let a : ℝ := r.left
    let b : ℝ := r.right
    let F : ℝ := (periodScores (mid r)).1
    let G : ℝ := (periodScores (mid r)).2
    (∫ P in 1/((k:ℝ)+b)..1/((k:ℝ)+a),smallTileWeight r k P) ≤
      (b-a)*(40*F/((k:ℝ)+a)^2+(F+G)/(2*((k:ℝ)+a)^3)) := by
  let a : ℝ := r.left
  let b : ℝ := r.right
  let f := linearProfile r
  let g := squareProfile r
  have ab : a<b := by dsimp [a,b]; exact_mod_cast (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1 : r.left < r.right)
  have hbpos : 0<(k:ℝ)+b := by linarith
  have kOrder : (k:ℝ)+a ≤ k+b := by linarith
  let H (y : ℝ) := smallTileWeight r k (1/y)*(1/y^2)
  let J (x : ℝ) := (40*(1/((k:ℝ)+a)^2))*f x + ((1/((k:ℝ)+a)^3)/2)*(f x+g x)
  have Hcont : ContinuousOn (fun x : ℝ => H (k+x)) (uIcc a b) := by
    rw [uIcc_of_le ab.le]
    intro x hx
    have hk : (k:ℝ)+x ≠ 0 := (lt_of_lt_of_le hpos (add_le_add_right hx.1 _)).ne'
    have hi : (1/((k:ℝ)+x)) ≠ 0 := one_div_ne_zero hk
    unfold H smallTileWeight linearProfile squareProfile realVal
    simp only [one_div_one_div,add_sub_cancel_left]
    fun_prop (disch := first | assumption | positivity | exact pow_ne_zero _ hk)
  have Jcont : Continuous J := by
    unfold J f g linearProfile squareProfile realVal
    fun_prop
  have comp : (∫ P in 1/((k:ℝ)+b)..1/((k:ℝ)+a),smallTileWeight r k P) = ∫ x in a..b,H (k+x) := by
    rw [OddZetaSix.integral_inv_sub _ hpos kOrder (smallTileWeight_continuous _ _ _ _ (by positivity))]
    exact (intervalIntegral.integral_comp_add_left H (k:ℝ)).symm
  have hle : (∫ x in a..b,H (k+x)) ≤ ∫ x in a..b,J x := by
    apply intervalIntegral.integral_mono_on ab.le Hcont.intervalIntegrable (Jcont.intervalIntegrable _ _)
    intro x hx
    have hkx : (k:ℝ)+a ≤ k+x := add_le_add_right hx.1 _
    have hy := hpos.trans_le hkx
    have he1 := one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hkx 2)
    have he2 := one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ hpos.le hkx 3)
    obtain ⟨hf,hg⟩ := profiles_nonneg r ok hx
    have hF := mul_le_mul_of_nonneg_right he1 (mul_nonneg (by norm_num : (0:ℝ)≤40) hf)
    have hG := mul_le_mul_of_nonneg_right he2 (add_nonneg hf hg)
    have hId : H (k+x) = (1/((k:ℝ)+x)^2)*(40*f x)+(1/((k:ℝ)+x)^3)*(f x+g x)/2 := by
      dsimp [H,smallTileWeight,f,g]
      rw [one_div_one_div,add_sub_cancel_left]
      field_simp [hy.ne']
    rw [hId]
    dsimp only [J]
    change 1/((k:ℝ)+x)^2*(40*f x) ≤ 1/((k:ℝ)+a)^2*(40*f x) at hF
    change 1/((k:ℝ)+x)^3*(f x+g x) ≤ 1/((k:ℝ)+a)^3*(f x+g x) at hG
    linarith only [hF,hG]
  have fc : Continuous f := continuous_realVal _
  have gc : Continuous g := continuous_realVal _
  have mean (L : Line) : (∫ x in a..b,realVal L x) = (b-a)*realVal L ((a+b)/2) := by
    unfold realVal
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,integral_id,intervalIntegral.integral_const,smul_eq_mul]; ring
  have hm : (mid r:ℝ)=(a+b)/2 := by simp [mid,a,b]
  have hmi : (mid r:ℝ) ∈ Ioo (r.left:ℝ) r.right := by
    change (mid r:ℝ) ∈ Ioo a b
    rw [hm]; constructor <;> linarith
  obtain ⟨hF,hG⟩ := smallRows_midpoint_integrals r hr
  have hdF : f ((a+b)/2) = ((periodScores (mid r)).1:ℝ) := by
    rw [← hm]; exact (period_integral_affine r ok linearTerm hmi).symm.trans hF.symm
  have hdG : g ((a+b)/2) = ((periodScores (mid r)).2:ℝ) := by
    rw [← hm]; exact (period_integral_affine r ok squareTerm hmi).symm.trans hG.symm
  change _ ≤ (b-a)*_
  rw [comp]
  apply hle.trans
  dsimp only [J]
  have hi : IntervalIntegrable (fun x => f x+g x) volume a b :=
    (fc.intervalIntegrable a b).add (gc.intervalIntegrable a b)
  rw [intervalIntegral.integral_add ((fc.intervalIntegrable a b).const_mul _) (hi.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (fc.intervalIntegrable a b) (gc.intervalIntegrable a b)]
  have mf : (∫ x in a..b,f x) = (b-a)*f ((a+b)/2) := mean _
  have mg : (∫ x in a..b,g x) = (b-a)*g ((a+b)/2) := mean _
  rw [mf,mg,hdF,hdG]
  apply le_of_eq
  simp only [div_eq_mul_inv,mul_inv_rev]; ring

end OddZetaSix.B40a.Cert.PeriodAffine
