import OddZetaSix.B40a.Analysis.GaussianEnergy
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

noncomputable section
namespace OddZetaSix.B40a
open Finset Filter MeasureTheory Set Real
open scoped Topology

theorem log_from_gaussian_cutoffs (A : ℝ) (hA : 0<A) :
    Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2,
      (Real.exp (-t)-Real.exp (-A*t))/t) ((𝓝[>] (0:ℝ)) ×ˢ atTop) (𝓝 (Real.log A)) := by
  let f (t : ℝ) := Real.exp (-t)
  have hc : Continuous f := by unfold f; fun_prop
  have h₀ : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    have hh := hc.continuousAt (x:=0)
    simpa [f] using (hh.continuousWithinAt (s:=Ioi 0)).tendsto
  have htop : Tendsto f atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have H := Frullani.tendsto_intervalIntegral (f:=f) (a:=1) (b:=A)
    (hc.locallyIntegrable.locallyIntegrableOn _) (by norm_num) hA h₀ htop
  simpa only [f,smul_eq_mul,sub_zero,mul_one,div_one,one_mul,neg_mul,div_eq_inv_mul,inv_one]
    using H

/-- The regularized planar log kernel is conditionally negative definite,
including when locations coincide. -/
theorem regularized_log_energy_nonpos {ι : Type*} [Fintype ι] (z : ι→ℂ) (a : ι→ℝ)
    (ha : ∑ i,a i=0) (η : ℝ) (hη : 0<η) :
    (∑ i,∑ j,a i*a j*Real.log (η+‖z i-z j‖^2)) ≤ 0 := by
  classical
  let A (i j : ι) := η+‖z i-z j‖^2
  let phi (i j : ι) (t : ℝ) := (Real.exp (-t)-Real.exp (-(A i j)*t))/t
  have hlim := tendsto_finsetSum (s:=(univ:Finset ι)) (fun i _ =>
    tendsto_finsetSum (s:=(univ:Finset ι)) (fun j _ =>
    (log_from_gaussian_cutoffs (A i j) (by dsimp [A]; positivity)).const_mul (a i*a j)))
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε := self_mem_nhdsWithin
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε ∧ ε≤1 :=
    hpos.and (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (by norm_num : (0:ℝ)<1)))
  filter_upwards [hε.prod_mk (eventually_ge_atTop (1:ℝ))] with p hp
  let b := p.1
  let c := p.2
  have hb : 0<b := hp.1.1
  have hbc : b≤c := hp.1.2.trans hp.2
  have hi (i j : ι) : IntervalIntegrable (fun t => a i*a j*phi i j t) volume b c := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hbc] at ht
    have ht0 : t≠0 := (hb.trans_le ht.1).ne'
    dsimp [phi]; fun_prop (disch := assumption)
  change (∑ i,∑ j, a i*a j * (∫ t in b..c, phi i j t)) ≤ _
  simp_rw [←intervalIntegral.integral_const_mul]
  simp_rw [←intervalIntegral.integral_finsetSum (fun j _ => hi _ j)]
  rw [←intervalIntegral.integral_finsetSum (fun i _ => (show
    IntervalIntegrable (fun t => ∑ j,a i*a j*phi i j t) volume b c by
    have he : (fun t => ∑ j,a i*a j*phi i j t)=(∑ j,fun t => a i*a j*phi i j t) := by funext t; simp
    rw [he]; exact IntervalIntegrable.sum univ (fun j _ => hi i j)))]
  rw [intervalIntegral.integral_of_le hbc]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioc (a:=b) (b:=c))] with t ht
  have ht0 : 0<t := hb.trans ht.1
  have hsplit (i j : ι) :
      a i*a j*phi i j t = (a i*a j*Real.exp (-t) -
        Real.exp (-η*t)*(a i*a j*Real.exp (-t*‖z i-z j‖^2)))/t := by
    unfold phi A
    rw [show -(η+‖z i-z j‖^2)*t = -η*t+ -t*‖z i-z j‖^2 by ring,Real.exp_add]; ring
  simp_rw [hsplit]
  simp only [←Finset.sum_div,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum,ha,zero_mul,zero_sub]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
    (mul_nonneg (Real.exp_pos _).le (gaussian_energy_nonneg z a t ht0.le))) ht0.le

end OddZetaSix.B40a
