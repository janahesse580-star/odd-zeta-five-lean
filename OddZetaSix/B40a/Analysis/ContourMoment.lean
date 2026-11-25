import OddZetaSix.B40a.Analysis.BentContour
import OddZetaSix.B40a.Analysis.MultipleIntegral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The finite bent-contour determinant as a multiple integral. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter MeasureTheory Set Complex Matrix Polynomial
open scoped BigOperators Topology Interval

abbrev BendEdge := Bool × Fin 8
abbrev BendParam := BendEdge × ℝ

def bendMeasure : Measure BendParam :=
  Measure.count.prod (volume.restrict (Ioc 0 1))

instance : IsFiniteMeasure bendMeasure := by
  unfold bendMeasure
  infer_instance

def edgeStart (n : ℕ) (e : BendEdge) : ℂ := bendNode n e.1 e.2

def edgeStop (n : ℕ) (q : ℝ) (e : BendEdge) : ℂ :=
  if h : e.2.val < 7 then bendNode n e.1 (⟨e.2.val+1,by omega⟩ : Fin 8)
  else pointAt e.1 (bendNodeX n 7) q

def edgeDelta (n : ℕ) (q : ℝ) (e : BendEdge) : ℂ := edgeStop n q e-edgeStart n e

def edgePoint (n : ℕ) (q : ℝ) (a : BendParam) : ℂ :=
  edgeStart n a.1+(a.2 : ℂ)*edgeDelta n q a.1

def bendWeight (n : ℕ) (q : ℝ) (a : BendParam) : ℂ :=
  (contourSide a.1.1 : ℂ)*edgeDelta n q a.1*contourIntegrand n 0 0 (edgePoint n q a)

def bendBasis (n : ℕ) (q : ℝ) (i : Fin (fiveRank n)) (a : BendParam) : ℂ :=
  aeval (edgePoint n q a + ((center n : ℕ) : ℂ)) (evenBasis i.val)

private theorem contourIntegrand_factor (n i j : ℕ) (z : ℂ) :
    contourIntegrand n i j z =
      aeval (z+((center n : ℕ) : ℂ)) (evenBasis i) *
      (aeval (z+((center n : ℕ) : ℂ)) (evenBasis j) * contourIntegrand n 0 0 z) := by
  simp only [contourIntegrand, entryComplex,kernelCenteredMultiplier,aeval_comp,map_mul,
    map_add,aeval_X,aeval_C]
  simp [center]
  ring

theorem edge_mem (n : ℕ) (q : ℝ) (hq : bendNodeY n 7 ≤ q) (e : BendEdge)
    (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
    edgePoint n q (e,t) ∈ bendDomain n e.1 := by
  apply segment_point_mem (convex_bendDomain n e.1) (bendNode_mem n e.1 _)
  · unfold edgeStop
    split_ifs with he
    · exact bendNode_mem n e.1 _
    · exact pointAt_mem_bendDomain n e.1 _ _ (bendNode_x_in_halfplane n 7)
        ((bendNode_offset_le n 7).trans (by linarith))
  · exact ht

theorem measurable_edgePoint (n : ℕ) (q : ℝ) : Measurable (edgePoint n q) := by
  unfold edgePoint
  exact ((measurable_of_countable (edgeStart n)).comp measurable_fst).add
    (Complex.continuous_ofReal.measurable.comp measurable_snd |>.mul
      ((measurable_of_countable (edgeDelta n q)).comp measurable_fst))

theorem measurable_contourIntegrand (n i j : ℕ) : Measurable (contourIntegrand n i j) := by
  unfold contourIntegrand entryComplex sixContourKernel
  have hp (P : ℚ[X]) : Measurable (fun z : ℂ => aeval z P) := by
    rw [show (fun z : ℂ => aeval z P) = fun z => (P.map (algebraMap ℚ ℂ)).eval z by
      ext z; rw [Polynomial.eval_map,aeval_def] ]
    exact (Polynomial.continuous _).measurable
  have hk : Measurable (iteratedDeriv 4 sixCotKernel) := by
    rw [show (4:ℕ) = 3+1 by decide,iteratedDeriv_succ]
    exact measurable_deriv _
  exact ((hp _).div (hp _)).mul (hk.div measurable_const)

def edgeIntegrand (n i j : ℕ) (q : ℝ) (a : BendParam) : ℂ :=
  contourSide a.1.1 * (contourIntegrand n i j (edgePoint n q a) * edgeDelta n q a.1)

theorem edgeIntegrand_integrable (n i j : ℕ) (q : ℝ) (hq : bendNodeY n 7 ≤ q) :
    Integrable (edgeIntegrand n i j q) bendMeasure := by
  have hm : Measurable (edgeIntegrand n i j q) := by
    unfold edgeIntegrand
    exact ((measurable_of_countable (fun e : BendEdge => (contourSide e.1 : ℂ))).comp measurable_fst).mul
      (((measurable_contourIntegrand n i j).comp (measurable_edgePoint n q)).mul
        ((measurable_of_countable (edgeDelta n q)).comp measurable_fst))
  unfold bendMeasure
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro e
    have hc : Continuous (fun t : ℝ => edgePoint n q (e,t)) := by unfold edgePoint; fun_prop
    have hd := (bend_continuousOn n i j e.1).comp hc.continuousOn (edge_mem n q hq e)
    have hh : ContinuousOn (fun t => edgeIntegrand n i j q (e,t)) (uIcc 0 1) :=
      (continuousOn_const (c := (contourSide e.1 : ℂ))).mul
        (hd.mul (continuousOn_const (c := edgeDelta n q e)))
    have hint := hh.intervalIntegrable (μ := volume)
    exact hint.1
  · exact Integrable.of_finite

theorem bendEntry_eq_integral (n : ℕ) (i j : Fin (fiveRank n)) (q : ℝ)
    (hq : bendNodeY n 7 ≤ q) :
    bentTruncation n i j q =
      ∫ a, bendBasis n q i a * (bendBasis n q j a * bendWeight n q a) ∂bendMeasure := by
  have he (a : BendParam) : bendBasis n q i a * (bendBasis n q j a * bendWeight n q a) =
      edgeIntegrand n i j q a := by
    unfold bendBasis bendWeight edgeIntegrand
    rw [contourIntegrand_factor n i j]
    ring
  simp_rw [he]
  have hi := edgeIntegrand_integrable n (i : ℕ) (j : ℕ) q hq
  unfold bendMeasure at hi ⊢
  rw [integral_prod _ hi,integral_count,Fintype.sum_prod_type,Fintype.sum_bool]
  have hside (s : Bool) :
      (∑ e : Fin 8, ∫ t in Ioc (0:ℝ) 1, edgeIntegrand n i j q ((s,e),t)) =
        (contourSide s : ℂ)*outwardPolygon (contourIntegrand n i j) n s q := by
    simp only [edgeIntegrand, ← intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
      intervalIntegral.integral_const_mul, ← Finset.mul_sum]
    unfold outwardPolygon
    congr 1
    rw [Fin.sum_univ_castSucc,bend_tail_eq_segment n i j s q hq]
    have hel (a : Fin 7) : edgeStop n q (s,a.castSucc) = bendNode n s a.succ := by
      unfold edgeStop
      simp only [Fin.val_castSucc,dite_eq_left a.isLt]
      rfl
    have helast : edgeStop n q (s,Fin.last 7) = pointAt s (bendNodeX n 7) q := by
      unfold edgeStop
      simp only [Fin.val_last,dite_eq_right (by decide : ¬ (7:ℕ) < 7)]
    simp only [straightSegment,edgePoint,edgeDelta,edgeStart,hel,helast]
    rfl
  rw [hside false,hside true]
  simp [contourSide,bentTruncation,sub_eq_add_neg,add_comm]

def bendMatrix (n : ℕ) (q : ℝ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℂ :=
  fun i j => bentTruncation n i j q

theorem det_bendMatrix_integral (n : ℕ) (q : ℝ) (hq : bendNodeY n 7 ≤ q) :
    ((fiveRank n).factorial : ℂ)*(bendMatrix n q).det =
      ∫ a : Fin (fiveRank n) → BendParam,
        ((sampleMatrix (bendBasis n q) a).det)^2 * ∏ j, bendWeight n q (a j)
        ∂Measure.pi (fun _ => bendMeasure) := by
  let f := bendBasis n q
  let g := fun (i : Fin (fiveRank n)) a => bendBasis n q i a*bendWeight n q a
  have hi (i j : Fin (fiveRank n)) : Integrable (fun a => f i a*g j a) bendMeasure := by
    have h (a : BendParam) : f i a*g j a = edgeIntegrand n i j q a := by
      unfold f g bendBasis bendWeight edgeIntegrand
      rw [contourIntegrand_factor n i j]
      ring
    simpa only [h] using edgeIntegrand_integrable n i j q hq
  have hmat : (Matrix.of (fun i j => ∫ a, f i a*g j a ∂bendMeasure)) = bendMatrix n q := by
    ext i j
    exact (bendEntry_eq_integral n i j q hq).symm
  rw [← hmat,← det_moment_integral bendMeasure f g hi]
  apply integral_congr_ae
  filter_upwards with a
  have hG : sampleMatrix g a = sampleMatrix f a * diagonal (fun j => bendWeight n q (a j)) := by
    ext i j
    simp [sampleMatrix,g,f]
  rw [hG,det_mul,det_diagonal]
  unfold f
  ring

theorem det_bendMatrix_tendsto (n : ℕ) :
    Tendsto (fun q : ℕ => (bendMatrix n q).det) atTop
      (𝓝 ((-(2*(Real.pi : ℂ)*Complex.I)) ^ fiveRank n * ((fiveFunctional n).map ofReal).det)) := by
  have hmat : Tendsto (fun q : ℕ => bendMatrix n q) atTop
    (𝓝 ((-(2*(Real.pi : ℂ)*Complex.I)) • (fiveFunctional n).map ofReal)) := by
    change Tendsto (fun q : ℕ => fun i j : Fin (fiveRank n) => bentTruncation n i j q) atTop
      (𝓝 (fun i j : Fin (fiveRank n) => -(2*(Real.pi : ℂ)*Complex.I)*(fiveFunctional n i j : ℂ)))
    exact tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => bentContour_eq_functional n i j))
  have hd := continuous_id.matrix_det.continuousAt.tendsto.comp hmat
  simpa only [Function.comp_def,id_eq,Matrix.det_smul,Fintype.card_fin] using hd

end OddZetaSix.B40a
