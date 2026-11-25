import OddZetaSix.B40a.Analysis.ScalarBudget
import OddZetaSix.B40a.Analysis.FiniteDensity
import OddZetaSix.B40a.Analysis.EdgeLength
import OddZetaSix.B40a.Analysis.ScalarReduction
import Mathlib.Data.EReal.Basic
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Real Finset MeasureTheory Filter Set
open scoped Topology Interval

private theorem finite_scalar (n : ℕ) (hn : 0<n) (hlarge : driftCost+1≤6*scaleN n)
    (q : ℝ) (hq : bendNodeY n 7≤q) (η : ℝ) (hη : 0<η) :
    oneIntegral n q ≤ 192*bentTrigConstant*(scaleN n)^2*
      Real.exp (scaleN n*((peak:ℝ)/fix)+blockError (scaleN n) η+5*driftCost+4) := by
  let D := scaleN n
  let U := 6*D*bentTrigConstant*Real.exp (D*((peak:ℝ)/fix)+blockError D η+5*driftCost+4)
  have hD : 0<D := by unfold D scaleN; positivity
  have ht := bentTrigConstant_positive.le
  have hu : 0≤U := by dsimp [U]; positivity
  have I := one_integrable n q hq
  unfold bendMeasure at I
  have rows := Measure.ae_count_iff.mp I.prod_right_ae
  have R (e : BendEdge) : ∫ t : ℝ in Ioc 0 1, oneWeight n q (e,t) ≤ U*(2*D) := by
    let f := fun t : ℝ=>U*lengthWeight n q (e,t)
    have hc : Continuous f := by dsimp [f,lengthWeight,edgeY,Cert.Chord.lerp]; fun_prop
    apply le_trans (b:=∫ t in Ioc 0 1, f t)
    · apply setIntegral_mono_on (rows e) (hc.intervalIntegrable (μ:=volume) 0 1).1 measurableSet_Ioc
      intro t ht
      exact edge_density n hn hlarge q hq e ⟨ht.1.le,ht.2⟩ hη
    ·
      unfold f; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (length_row n hn q hq e) hu
  unfold oneIntegral bendMeasure
  rw [integral_prod _ I,integral_count]
  apply (sum_le_sum (s:=univ) (fun e _=>R e)).trans_eq
  simp [U,D,Fintype.card_prod]; ring

theorem scalar_peak : ScalarPeak := by
  intro δ hδ
  obtain ⟨η,hη,hbudget⟩ := absorb_scalar_budget ((peak:ℝ)/fix) bentTrigConstant (5*driftCost+4) δ bentTrigConstant_positive hδ
  have G := scale_tendsto.eventually (eventually_ge_atTop (driftCost+1))
  filter_upwards [eventually_gt_atTop (0:ℕ),hbudget,G] with n hn hB hG
  have D : 0<scaleN n := by unfold scaleN; positivity
  have big : driftCost+1≤6*scaleN n := by linarith only [hG,D]
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (bendNodeY n 7))] with q hq
  apply (finite_scalar n hn big q hq η hη).trans
  simpa only [scaleN,add_assoc] using hB
end OddZetaSix.B40a.Witness

namespace OddZetaSix.B40a
open Filter
theorem determinant_analytic_rate :
    ∀ᶠ n : ℕ in atTop, |(fiveFunctional n).det| ≤ Real.exp ((-619/100:ℝ)*normalizer n) :=
  Witness.det_exp_of_scalar_peak Witness.scalar_peak

/-- The logarithm of a zero determinant is minus infinity on the extended
real scale used in this asymptotic estimate. -/
def logDetRate (n : ℕ) : EReal :=
  if (fiveFunctional n).det=0 then ⊥ else ((Real.log |(fiveFunctional n).det|/normalizer n:ℝ):EReal)

theorem determinant_analytic_limsup :
    limsup logDetRate atTop ≤ ((-619/100:ℝ):EReal) := by
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [determinant_analytic_rate,eventually_gt_atTop (0:ℕ)] with n H hn
  unfold logDetRate; split_ifs with h
  · exact bot_le
  · apply EReal.coe_le_coe_iff.mpr
    apply (div_le_iff₀ (by unfold normalizer; positivity)).mpr
    exact (Real.log_le_iff_le_exp (abs_pos.mpr h)).mpr H
end OddZetaSix.B40a
