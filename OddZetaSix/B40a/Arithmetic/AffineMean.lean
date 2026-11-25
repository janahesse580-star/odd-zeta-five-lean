import OddZetaSix.B40a.Arithmetic.PeriodicAffine


namespace OddZetaSix.B40a.Cert
open Set MeasureTheory

private theorem affine_mean (L : PeriodAffine.Line) (a b : ℝ) :
    (∫ t in a..b, PeriodAffine.realVal L t) = (b-a)*PeriodAffine.realVal L ((a+b)/2) := by
  unfold PeriodAffine.realVal
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    intervalIntegrable_const,intervalIntegral.integral_const_mul,integral_id,
    intervalIntegral.integral_const,smul_eq_mul]
  ring

theorem mean_of_affine_check (r : ArithRow) (ok : PeriodAffine.check r = true) (F : ℤ → ℤ) :
    (∫ t in (r.left:ℝ)..r.right, ∫ u in (0:ℝ)..1, (F (periodicScore t u):ℝ)) =
      ((r.right:ℝ)-r.left)*(∫ u in (0:ℝ)..1, (F (periodicScore (PeriodAffine.mid r:ℝ) u):ℝ)) := by
  have h : r.left < r.right := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1
  have hR : (r.left:ℝ)<r.right := by exact_mod_cast h
  have hm : (PeriodAffine.mid r:ℝ) = ((r.left:ℝ)+r.right)/2 := by
    simp [PeriodAffine.mid]
  have ht : (PeriodAffine.mid r:ℝ) ∈ Ioo (r.left:ℝ) (r.right:ℝ) := by
    rw [hm]; constructor <;> linarith
  rw [intervalIntegral.integral_congr_Ioo_of_le hR.le (fun t ht =>
    PeriodAffine.period_integral_affine r ok F ht),
    affine_mean,PeriodAffine.period_integral_affine r ok F ht,hm]

end OddZetaSix.B40a.Cert
