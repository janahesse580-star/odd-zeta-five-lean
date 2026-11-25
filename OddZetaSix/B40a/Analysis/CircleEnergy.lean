import OddZetaSix.B40a.Analysis.CircleQuadrature

noncomputable section
namespace OddZetaSix.B40a
open Filter Finset Set MeasureTheory Real
open scoped Topology
namespace Orbit

def tracePoint (u : ℂ) (r x : ℝ) := circleMap u r (2*π*x)

theorem trace_integral (f : ℂ→ℝ) (u : ℂ) (r : ℝ) :
    (∫ x in (0:ℝ)..1, f (tracePoint u r x))=circleAverage f u r := by
  unfold tracePoint circleAverage
  simpa only [mul_zero,mul_one] using intervalIntegral.integral_comp_mul_left
    (fun t=>f (circleMap u r t)) (a:=(0:ℝ)) (b:=1) (by positivity : 2*π≠0)

def logKernel (η : ℝ) (z w : ℂ) := Real.log (η+‖z-w‖^2)
def orbitEnergy (η : ℝ) (u v : ℂ) (r s : ℝ) : ℝ :=
  circleAverage (fun z=>circleAverage (logKernel η z) v s) u r

theorem logKernel_cont {η : ℝ} (hη : 0<η) : Continuous (Function.uncurry (logKernel η)) := by
  apply Continuous.log (continuous_const.add ((continuous_fst.sub continuous_snd).norm.pow 2))
  intro z; exact (add_pos_of_pos_of_nonneg hη (sq_nonneg _)).ne'

theorem energy_limit (η : ℝ) (hη : 0<η) (u v : ℂ) (r s : ℝ) :
    Tendsto (fun n : ℕ=>avg n (fun x=>avg n (fun y=>
      logKernel η (tracePoint u r x) (tracePoint v s y)))) atTop (𝓝 (orbitEnergy η u v r s)) := by
  let F := fun z : ℝ×ℝ=>logKernel η (tracePoint u r z.1) (tracePoint v s z.2)
  have c (u : ℂ) (r : ℝ) : Continuous (tracePoint u r) :=
    (continuous_circleMap u r).comp (continuous_const.mul continuous_id)
  have hF : Continuous F := (logKernel_cont hη).comp (((c u r).comp continuous_fst).prodMk
    ((c v s).comp continuous_snd))
  have H := double_tendsto F hF
  have eq : (∫ x in (0:ℝ)..1,∫ y in (0:ℝ)..1,F (x,y))=orbitEnergy η u v r s := by
    simp only [F,trace_integral,orbitEnergy]
    exact trace_integral (fun z=>circleAverage (logKernel η z) v s) u r
  rw [eq] at H
  exact H

end Orbit
open Orbit

/-- The regularized log-energy inequality for *continuous uniform circles*.
Convergence uses one common polygon order for all signed interactions. -/
theorem regularized_circle_energy_nonpos {ι : Type*} [Fintype ι]
    (u : ι→ℂ) (r a : ι→ℝ) (ha : ∑ i,a i=0) (η : ℝ) (hη : 0<η) :
    (∑ i,∑ j,a i*a j*orbitEnergy η (u i) (u j) (r i) (r j)) ≤ 0 := by
  classical
  let K (i j : ι) (x y : ℝ) := logKernel η (tracePoint (u i) (r i) x) (tracePoint (u j) (r j) y)
  have H := tendsto_finsetSum (s:=(univ:Finset ι)) (fun i _=>tendsto_finsetSum (s:=(univ:Finset ι))
    (fun j _=>(energy_limit η hη (u i) (u j) (r i) (r j)).const_mul (a i*a j)))
  apply le_of_tendsto H
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  let Z (i : ι × Fin n) := tracePoint (u i.1) (r i.1) (grid n i.2)
  let w (i : ι × Fin n) := a i.1/(n:ℝ)
  have hmass : ∑ i,w i=0 := by
    simp only [w,Fintype.sum_prod_type,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    simpa only [mul_div_cancel₀ _ hp, mul_div_assoc'] using ha
  have L := regularized_log_energy_nonpos Z w hmass η hη
  change (∑ i,∑ j,a i*a j*avg n (fun x=>avg n (fun y=>K i j x y)))≤0
  apply le_trans _ L
  apply le_of_eq
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl; intro i _
  rw [Finset.sum_comm (f:=fun k j=>∑ l : Fin n,w (i,k)*w (j,l)*Real.log (η+‖Z (i,k)-Z (j,l)‖^2))]
  apply sum_congr rfl; intro j _
  simp only [avg,div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum,
    w,Z,K,logKernel]
  apply sum_congr rfl; intro k _
  apply sum_congr rfl; intro l _
  ring
end OddZetaSix.B40a
