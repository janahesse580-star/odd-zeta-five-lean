import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! Circle average and perturbation estimates for the logarithmic potential. -/
noncomputable section
namespace OddZetaSix.B40a
open MeasureTheory Filter Metric Set Complex Real
open scoped Topology

def circlePotential (u : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  Real.log (max r ‖z-u‖)

theorem circlePotential_eq_average (u z : ℂ) (r : ℝ) (hr : 0<r) :
    circleAverage (fun w => Real.log ‖w-z‖) u r = circlePotential u r z := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne',circlePotential]
  have hnorm : ‖u-z‖ = ‖z-u‖ := norm_sub_rev _ _
  rw [hnorm]
  by_cases h : ‖z-u‖ ≤ r
  · rw [max_eq_left h, (Real.posLog_eq_zero_iff _).mpr]
    · exact add_zero _
    · rw [inv_mul_eq_div,abs_of_nonneg (div_nonneg (norm_nonneg _) hr.le),div_le_one hr]
      exact h
  · have hh : r ≤ ‖z-u‖ := (lt_of_not_ge h).le
    have hp : 0 < ‖z-u‖ := hr.trans_le hh
    rw [max_eq_right hh, Real.posLog_eq_log (by rw [inv_mul_eq_div,abs_of_nonneg (div_nonneg hp.le hr.le),le_div_iff₀ hr,one_mul]; exact hh),
      inv_mul_eq_div, Real.log_div hp.ne' hr.ne']
    ring

theorem continuous_circlePotential (u : ℂ) (r : ℝ) (hr : 0<r) :
    Continuous (circlePotential u r) :=
  continuous_iff_continuousAt.mpr fun _z =>
    (((continuous_const.max ((continuous_id.sub continuous_const).norm)).continuousAt).log
      (hr.trans_le (le_max_left _ _)).ne')

theorem circlePotential_le_add_dist (u v z : ℂ) (r : ℝ) (hr : 0<r) :
    circlePotential u r z ≤ circlePotential u r v + ‖z-v‖/r := by
  let a := max r ‖z-u‖
  let b := max r ‖v-u‖
  let d := ‖z-v‖
  have hb : r ≤ b := le_max_left _ _
  have ha0 : 0 < a := hr.trans_le (le_max_left _ _)
  have hb0 : 0 < b := hr.trans_le hb
  have hd : 0 ≤ d := norm_nonneg _
  have hab : a ≤ b+d := by
    apply max_le (hb.trans (le_add_of_nonneg_right hd))
    have h : ‖z-u‖ ≤ ‖z-v‖+‖v-u‖ := by
      rw [show z-u = (z-v)+(v-u) by ring]
      exact norm_add_le _ _
    exact h.trans (by have hv : ‖v-u‖ ≤ b := le_max_right _ _; linarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hlog
  have hdiv : a/b-1 ≤ d/b := by
    have h1 := div_le_div_of_nonneg_right hab hb0.le
    rw [add_div,div_self hb0.ne'] at h1
    linarith
  have hbd := div_le_div_of_nonneg_left hd hr hb
  change Real.log a ≤ Real.log b + d/r
  linarith

theorem circleSelfEnergy (u : ℂ) (r : ℝ) (hr : 0<r) :
    circleAverage (circlePotential u r) u r = Real.log r := by
  apply circleAverage_const_on_circle
  intro z hz
  have h := (show ‖z-u‖ = |r| by simpa only [Metric.mem_sphere,dist_eq_norm] using hz)
  rw [abs_of_pos hr] at h
  rw [circlePotential,h,max_self]

theorem circlePotential_average_le (u v : ℂ) (r ε : ℝ) (hr : 0<r) (hε : 0<ε) :
    circleAverage (circlePotential u r) v ε ≤ circlePotential u r v + ε/r := by
  rw [← circleAverage_const (circlePotential u r v + ε/r) v ε]
  apply circleAverage_mono (continuous_circlePotential u r hr).continuousOn.circleIntegrable'
    continuousOn_const.circleIntegrable'
  intro z hz
  have h := circlePotential_le_add_dist u v z r hr
  rw [(show ‖z-v‖ = |ε| by simpa only [Metric.mem_sphere,dist_eq_norm] using hz),abs_of_pos hε] at h
  exact h

theorem circleInteraction_ge_log (u v : ℂ) (r s : ℝ) (hr : 0<r) (hs : 0<s) (huv : v≠u) :
    Real.log ‖v-u‖ ≤ circleAverage (circlePotential u r) v s := by
  let g : ℂ → ℝ := fun z => if z=u then circlePotential u r z else Real.log ‖z-u‖
  have he : (fun z : ℂ => Real.log ‖z-u‖) =ᶠ[codiscreteWithin (Metric.sphere v |s|)] g := by
    have hh : {z : ℂ | z ≠ u} ∈ codiscreteWithin (Metric.sphere v |s|) := by
      apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
      intro x hx
      use Set.univ
      simp only [univ_mem, Set.univ_inter, true_and]
      exact (Set.finite_singleton u).subset (by intro y hy; exact Set.mem_singleton_iff.mpr (by simpa using hy.2))
    filter_upwards [hh] with z hz
    exact (ite_eq_right hz).symm
  have hg : CircleIntegrable g v s :=
    (circleIntegrable_congr_codiscreteWithin he).mp (circleIntegrable_log_norm_sub_const s)
  have hle : circleAverage g v s ≤ circleAverage (circlePotential u r) v s := by
    apply circleAverage_mono hg (continuous_circlePotential u r hr).continuousOn.circleIntegrable'
    intro z _
    by_cases hzu : z=u
    · simp [g,hzu]
    · simp only [g,ite_eq_right hzu,circlePotential]
      exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hzu)) (le_max_right _ _)
  rw [← circleAverage_congr_codiscreteWithin he hs.ne',circlePotential_eq_average v u s hs] at hle
  apply le_trans _ hle
  rw [circlePotential,norm_sub_rev u v]
  exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr huv)) (le_max_right _ _)

end OddZetaSix.B40a
