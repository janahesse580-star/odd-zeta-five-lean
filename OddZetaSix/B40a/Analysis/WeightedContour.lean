import OddZetaSix.B40a.Analysis.WitnessEnergy

noncomputable section
namespace OddZetaSix.B40a.Witness
open Finset MeasureTheory Filter Set Matrix
open scoped Topology

def oneWeight (n : ℕ) (q : ℝ) (a : BendParam) :=
  Real.exp (2*(fiveRank n:ℝ)*potential (bendScaledSquare n q a))*‖bendWeight n q a‖
def oneIntegral (n : ℕ) (q : ℝ) := ∫ a,oneWeight n q a ∂bendMeasure
def correction (n : ℕ) (ε : ℝ) := 2*(fiveRank n:ℝ)^2*ε*errorSlope-(fiveRank n:ℝ)*Real.log ε
def pref (n : ℕ) (ε : ℝ) := Real.exp (correction n ε-(fiveRank n:ℝ)^2*energy)

theorem potential_cont : Continuous potential := by
  unfold potential
  exact continuous_finsetSum _ (fun k _=>continuous_const.mul (continuous_circlePotential _ _ (valid k).1))

theorem one_integrable (n : ℕ) (q : ℝ) (hq : bendNodeY n 7≤q) : Integrable (oneWeight n q) bendMeasure := by
  have hc : Measurable (bendScaledSquare n q) := by
    unfold bendScaledSquare
    exact (((measurable_edgePoint n q).add measurable_const).div measurable_const).pow_const 2
  have hm : Measurable (oneWeight n q) := by
    unfold oneWeight bendWeight
    have side : Measurable (fun a : BendParam=>(contourSide a.1.1:ℂ)) :=
      (measurable_of_countable (fun e : BendEdge=>(contourSide e.1:ℂ))).comp measurable_fst
    have delta : Measurable (fun a : BendParam=>edgeDelta n q a.1) :=
      (measurable_of_countable (edgeDelta n q)).comp measurable_fst
    exact (Real.measurable_exp.comp (measurable_const.mul (potential_cont.measurable.comp hc))).mul
      ((side.mul delta).mul ((measurable_contourIntegrand n 0 0).comp (measurable_edgePoint n q))).norm
  apply (integrable_prod_iff (μ:=Measure.count) (ν:=volume.restrict (Ioc 0 1)) hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun e=>?_),Integrable.of_finite⟩
  have c : Continuous (fun t : ℝ=>edgePoint n q (e,t)) := by unfold edgePoint; fun_prop
  have cs : Continuous (fun t : ℝ=>bendScaledSquare n q (e,t)) := by unfold bendScaledSquare; fun_prop
  have ce := (bend_continuousOn n 0 0 e.1).comp c.continuousOn (edge_mem n q hq e)
  have ew : ContinuousOn (fun t : ℝ=>bendWeight n q (e,t)) (uIcc 0 1) :=
    (continuousOn_const (c:=(contourSide e.1:ℂ)*edgeDelta n q e)).mul ce
  have ci : ContinuousOn (fun t : ℝ=>oneWeight n q (e,t)) (uIcc 0 1) :=
    ((continuous_const.mul (potential_cont.comp cs)).rexp.continuousOn).mul ew.norm
  exact (ci.intervalIntegrable (μ:=volume)).1

theorem pref_product (n : ℕ) (q : ℝ) (a : Fin (fiveRank n)→BendParam) {ε : ℝ} (hε : 0<ε) :
    ‖bendVandermondeIntegrand n q a‖ ≤ pref n ε*∏ i,oneWeight n q (a i) := by
  apply (integrand_bound n q a hε).trans_eq
  unfold pref oneWeight
  rw [prod_mul_distrib,←mul_assoc,←Real.exp_sum,←Real.exp_add,←mul_sum]
  congr 2
  unfold correction; ring

/-- Finite-height reduction to a single real integral, without an assumed
majorant, a positivity assumption on the determinant, or omitted diagonals. -/
theorem finite_det_bound (n : ℕ) (hn : 0<n) (q : ℝ) (hq : bendNodeY n 7≤q)
    {ε : ℝ} (hε : 0<ε) :
    ((fiveRank n).factorial:ℝ)*‖(bendMatrix n q).det‖ ≤
      basisNormalization n*pref n ε*(oneIntegral n q)^fiveRank n := by
  have H := det_bendMatrix_scaled_vandermonde n hn q hq
  have I := (Integrable.fintype_prod (fun _ : Fin (fiveRank n)=>one_integrable n q hq)).const_mul (pref n ε)
  have hb := norm_integral_le_of_norm_le I (Eventually.of_forall (fun a=>pref_product n q a hε))
  rw [integral_const_mul,integral_fintype_prod_eq_prod] at hb
  simp only [prod_const,card_univ,Fintype.card_fin] at hb
  change ‖∫ a,bendVandermondeIntegrand n q a ∂_‖ ≤ pref n ε*(oneIntegral n q)^fiveRank n at hb
  have heq := congrArg norm H
  simp only [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (basisNormalization_pos _ hn)] at heq
  rw [heq,mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (basisNormalization_pos n hn).le

theorem correction_rate :
    Tendsto (fun n : ℕ=>correction n (1/(n:ℝ))/normalizer n) atTop (𝓝 0) := by
  have L : Tendsto (fun n : ℕ=>Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq] using!
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have H := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (8/5*errorSlope)
  have HH := H.add (L.const_mul (1/50))
  simp only [mul_zero,add_zero] at HH
  apply HH.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold correction fiveRank normalizer
  rw [one_div,Real.log_inv]
  push_cast
  field_simp
  <;> ring
end OddZetaSix.B40a.Witness
