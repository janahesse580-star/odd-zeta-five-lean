import OddZetaSix.B40a.Analysis.CircleEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace OddZetaSix.B40a.Orbit
open Filter Set MeasureTheory Real
open scoped Topology

def eta (n : ℕ) : ℝ := 1/((n:ℝ)+1)
theorem eta_pos (n : ℕ) : 0<eta n := by unfold eta; positivity
theorem eta_anti : Antitone eta := by
  intro m n h
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

def angles := volume.restrict (Ioc (0:ℝ) (2*π))

private theorem ae_circle_ne (u z : ℂ) {r : ℝ} (hr : r≠0) :
    ∀ᵐ x ∂angles, circleMap u r x ≠ z := by
  apply ae_restrict_le_codiscreteWithin measurableSet_Ioc
  apply codiscreteWithin_mono (show Ioc (0:ℝ) (2*π) ⊆ univ from subset_univ _)
  exact circleMap_preimage_codiscrete hr (compl_singleton_mem_codiscreteWithin z)

private theorem circleInt {f : ℂ→ℝ} {u : ℂ} {r : ℝ} (h : CircleIntegrable f u r) :
    Integrable (fun x=>f (circleMap u r x)) angles := h.1

/-- A decreasing family can be integrated down to an integrable logarithmic
singularity. Coincident points are excluded only on a null set of angles. -/
private theorem decreasing_avg (f : ℕ→ℂ→ℝ) (g : ℂ→ℝ) (u : ℂ) (r : ℝ)
    (hf : ∀ n,CircleIntegrable (f n) u r) (hg : CircleIntegrable g u r)
    (hanti : ∀ w,Antitone (fun n=>f n w))
    (hlim : ∀ᵐ x ∂angles,Tendsto (fun n=>f n (circleMap u r x)) atTop (𝓝 (g (circleMap u r x)))) :
    Tendsto (fun n=>circleAverage (f n) u r) atTop (𝓝 (circleAverage g u r)) := by
  let b := fun x=>‖g (circleMap u r x)‖+‖f 0 (circleMap u r x)‖
  have hb : Integrable b angles := (circleInt hg).norm.add (circleInt (hf 0)).norm
  have H := tendsto_integral_of_dominated_convergence (μ:=angles) b
    (fun n=>(circleInt (hf n)).aestronglyMeasurable) hb (fun n=>by
      filter_upwards [hlim] with x hx
      let w := circleMap u r x
      have hu := hanti w (Nat.zero_le n)
      have hl := (hanti w).le_of_tendsto hx n
      change |f n w|≤|g w|+|f 0 w|
      exact abs_le.mpr ⟨by linarith only [hl,neg_abs_le (g w),abs_nonneg (f 0 w)],
        by linarith only [hu,le_abs_self (f 0 w),abs_nonneg (g w)]⟩) hlim
  simpa only [circleAverage,intervalIntegral.integral_of_le (by positivity : 0≤2*π),smul_eq_mul,angles] using
    H.const_mul ((2*π)⁻¹)

theorem kernel_anti (z w : ℂ) : Antitone (fun n=>logKernel (eta n) z w) := by
  intro i j h
  exact Real.log_le_log (add_pos_of_pos_of_nonneg (eta_pos j) (sq_nonneg _))
    (add_le_add_left (eta_anti h) _)

def innerMean (n : ℕ) (v : ℂ) (s : ℝ) (z : ℂ) := circleAverage (logKernel (eta n) z) v s

private theorem kernel_ci (n : ℕ) (z v : ℂ) (s : ℝ) : CircleIntegrable (logKernel (eta n) z) v s :=
  ((logKernel_cont (eta_pos n)).comp (continuous_const.prodMk continuous_id)).continuousOn.circleIntegrable'

theorem inner_limit (v z : ℂ) (s : ℝ) (hs : 0<s) :
    Tendsto (fun n=>innerMean n v s z) atTop (𝓝 (2*circlePotential v s z)) := by
  let g := fun w : ℂ=>(2:ℝ)*Real.log ‖w-z‖
  have hg : CircleIntegrable g v s := (circleIntegrable_log_norm_sub_const (a:=z) (c:=v) s).const_mul 2
  have H := decreasing_avg (fun n=>logKernel (eta n) z) g v s (fun n=>kernel_ci n _ _ _) hg
    (kernel_anti z) (by
      filter_upwards [ae_circle_ne v z hs.ne'] with x hx
      let w := circleMap v s x
      have hw : 0<‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
      have hseq : Tendsto eta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have ht := ((hseq.add_const (‖z-w‖^2)).log (by simp [hw.ne'] : 0+‖z-w‖^2≠0))
      simpa only [logKernel,g,w,zero_add,Real.log_pow,Nat.cast_ofNat,norm_sub_rev z] using ht)
  have he : circleAverage g v s=2*circlePotential v s z := by
    change circleAverage (fun w=>(2:ℝ) • Real.log ‖w-z‖) v s=_
    rw [circleAverage_fun_smul,circlePotential_eq_average _ _ _ hs,smul_eq_mul]
  rwa [he] at H

theorem inner_cont (n : ℕ) (v : ℂ) (s : ℝ) : Continuous (innerMean n v s) := by
  let F := fun z : ℂ=>fun y : ℝ=>logKernel (eta n) z (circleMap v s y)
  have c : Continuous F.uncurry := (logKernel_cont (eta_pos n)).comp
    (continuous_fst.prodMk ((continuous_circleMap v s).comp continuous_snd))
  have H := (continuous_parametric_integral_of_continuous (μ:=volume) c (isCompact_Icc (a:=0) (b:=2*π))).const_mul ((2*π)⁻¹)
  change Continuous (fun z=>circleAverage (logKernel (eta n) z) v s)
  simpa only [innerMean,circleAverage,intervalIntegral.integral_of_le (by positivity : 0≤2*π),
    integral_Icc_eq_integral_Ioc,smul_eq_mul,F] using H

def interaction (u v : ℂ) (r s : ℝ) := circleAverage (circlePotential v s) u r

theorem interaction_limit (u v : ℂ) (r s : ℝ) (hs : 0<s) :
    Tendsto (fun n=>orbitEnergy (eta n) u v r s) atTop (𝓝 (2*interaction u v r s)) := by
  have H := decreasing_avg (fun n=>innerMean n v s) (fun z=>2*circlePotential v s z) u r
    (fun n=>(inner_cont n v s).continuousOn.circleIntegrable')
    ((continuous_const.mul (continuous_circlePotential v s hs)).continuousOn.circleIntegrable') (by
      intro z i j hij
      exact circleAverage_mono (kernel_ci j z v s) (kernel_ci i z v s) (fun w _=>kernel_anti z w hij))
    (Eventually.of_forall fun x=>inner_limit v _ s hs)
  change Tendsto _ _ (𝓝 (circleAverage (fun z=>(2:ℝ) • circlePotential v s z) u r)) at H
  rwa [circleAverage_fun_smul,smul_eq_mul] at H

end OddZetaSix.B40a.Orbit

namespace OddZetaSix.B40a
open Filter Finset Orbit
open scoped Topology

/-- Logarithmic energy of any zero-mass signed sum of uniform circles,
with their actual self-interactions and no regularization term. -/
theorem signed_circle_energy_nonpos {ι : Type*} [Fintype ι]
    (u : ι→ℂ) (r a : ι→ℝ) (hr : ∀ i,0<r i) (ha : ∑ i,a i=0) :
    (∑ i,∑ j,a i*a j*interaction (u i) (u j) (r i) (r j)) ≤ 0 := by
  have H := tendsto_finsetSum (s:=(univ:Finset ι)) (fun i _=>tendsto_finsetSum (s:=(univ:Finset ι))
    (fun j _=>(interaction_limit (u i) (u j) (r i) (r j) (hr j)).const_mul (a i*a j)))
  have neg := le_of_tendsto H (Eventually.of_forall fun n=>regularized_circle_energy_nonpos u r a ha _ (eta_pos n))
  simp only [show ∀ x y : ℝ,x*(2*y)=2*(x*y) from fun x y=>by ring,←Finset.mul_sum] at neg
  linarith
end OddZetaSix.B40a
