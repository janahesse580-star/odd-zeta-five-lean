import OddZetaSix.B40a.Analysis.EdgeCoordinates
import OddZetaSix.B40a.Analysis.KernelPhase
import OddZetaSix.B40a.Analysis.WeightedContour
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Cert.Chord Set Real Finset

def driftCost : ℝ := 32*(errorSlope+1)
private theorem slope_pos : 0≤errorSlope := sum_nonneg fun i _=>div_nonneg (valid i).2 (valid i).1.le
theorem driftCost_pos : 0<driftCost := by unfold driftCost; linarith only [slope_pos]

private theorem absorb_height (D y : ℝ) (_hy : 0≤y) (hD : driftCost+1≤6*D) :
    -6*D*max (y-4) 0+driftCost*(1+y)≤5*driftCost+4-y := by
  let v := max (y-4) 0
  have h1 : y≤4+v := by linarith only [le_max_left (y-4) 0]
  have hv : 0≤v := le_max_right _ _
  nlinarith only [mul_le_mul_of_nonneg_right hD hv,mul_le_mul_of_nonneg_left h1 driftCost_pos.le,h1]

theorem edge_density (n : ℕ) (hn : 0<n) (hlarge : driftCost+1≤6*scaleN n)
    (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge) {t : ℝ} (ht : t∈Set.Icc 0 1) {η : ℝ} (hη : 0<η) :
    oneWeight n q (e,t) ≤
      (6*scaleN n*bentTrigConstant*Real.exp
        (scaleN n*((peak:ℝ)/fix)+blockError (scaleN n) η+5*driftCost+4))*
      (‖edgeDelta n q e‖*Real.exp (-edgeY n q e.2 t)) := by
  let x := edgeX e.2 t
  let y := edgeY n q e.2 t
  let z := edgePoint n q (e,t)
  let D := scaleN n
  let v := pointAt e.1 x y
  let θ := anchorDrift n
  have D0 : 0<D := by unfold D scaleN; positivity
  have N : (1:ℝ)≤n := by exact_mod_cast hn
  have D2 : 2≤D := by dsimp [D,scaleN]; linarith only [N]
  have hc : Coordinates n z x y θ := edge_coordinates n hn q hq e ht
  have hθ : θ≤1 := hc.drift_high.trans ((div_le_one D0).mpr D2)
  have hcen := (edge_affine n hn q e t).1
  change z.re+(OddZetaSix.B40a.center n:ℝ)=D*(x+θ) at hcen
  have cen : ‖z+(OddZetaSix.B40a.center n:ℂ)‖≤3*D*Real.exp y := by
    have U := Complex.norm_le_abs_re_add_abs_im (z+(OddZetaSix.B40a.center n:ℂ))
    simp only [Complex.add_re,Complex.natCast_re,Complex.add_im,Complex.natCast_im,add_zero,hcen,hc.imag_eq] at U
    have hpos : 0≤D*(x+θ) := mul_nonneg D0.le (add_nonneg (by linarith only [hc.x_low]) hc.drift_low)
    rw [abs_of_nonneg hpos] at U
    apply U.trans
    have E := Real.add_one_le_exp y
    have H : x+θ+y≤3*Real.exp y := by linarith only [E,hc.y_nonneg,hc.x_high,hθ]
    linear_combination D*H
  have vv : ‖v‖≤2+y := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |(pointAt e.1 x y).re|+|(pointAt e.1 x y).im|≤_
    rw [pointAt_re,pointAt_im,abs_mul,abs_of_nonneg hc.y_nonneg,abs_of_nonneg (by linarith only [hc.x_low] : 0≤x)]
    have hs : |contourSide e.1|=1 := by cases e.1 <;> norm_num [contourSide]
    rw [hs,one_mul]; linarith only [hc.x_high]
  have hh : 2*(fiveRank n:ℝ)=(8/5)*D := by unfold fiveRank D scaleN; push_cast; ring
  have Q := potential_square_shift v (θ:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc.drift_low] at Q
  have θD : θ*D≤2 := (le_div_iff₀ D0).mp hc.drift_high
  have vc : 2*‖v‖+θ≤5+2*y := by linarith only [vv,hθ]
  have prod := mul_le_mul θD vc (by linarith only [norm_nonneg v,hc.drift_low]) (by norm_num : (0:ℝ)≤2)
  have QE : (8/5)*D*potential ((v+(θ:ℂ))^2)+y ≤
      (8/5)*D*potential (v^2)+driftCost*(1+y) := by
    have J := mul_le_mul_of_nonneg_left Q (show 0≤(8/5)*D by positivity)
    have G := mul_le_mul_of_nonneg_left prod slope_pos
    unfold driftCost
    nlinarith only [J,G,slope_pos,hc.y_nonneg,mul_nonneg slope_pos hc.y_nonneg]
  have field := edge_field_bound n hn q hq e ht
  change phaseReal x y+(8/5)*potential (v^2)≤(peak:ℝ)/fix-6*max (y-4) 0 at field
  have fb := mul_le_mul_of_nonneg_left field D0.le
  have hf := absorb_height D y hc.y_nonneg hlarge
  have hd := base_phase_bound hn hc hη
  have hk := edge_trig_decay n q hq e ht
  change ‖sixContourKernel z‖≤bentTrigConstant*Real.exp (-2*Real.pi*|z.im|) at hk
  rw [hc.imag_eq] at hk
  change ‖entryComplex n 0 0 z‖≤2*‖z+(OddZetaSix.B40a.center n:ℂ)‖*Real.exp (D*(phaseReal x y+2*y*Real.pi)+blockError D η) at hd
  have HJ := hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cen (by norm_num : (0:ℝ)≤2)) (Real.exp_pos _).le)
  have trigpos := bentTrigConstant_positive.le
  have hg := mul_le_mul HJ hk (norm_nonneg _) (by positivity)
  let d := ‖edgeDelta n q e‖
  have S : ‖(contourSide e.1:ℂ)‖=1 := by cases e.1 <;> norm_num [contourSide]
  unfold oneWeight bendWeight contourIntegrand
  rw [edge_square n hn,hh,norm_mul,norm_mul,norm_mul,S,one_mul]
  change Real.exp ((8/5)*D*potential ((v+(θ:ℂ))^2))*(d*(‖entryComplex n 0 0 z‖*‖sixContourKernel z‖))≤_
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) (Real.exp_pos _).le).trans
  let P := (8/5)*D*potential ((v+(θ:ℂ))^2)
  let K := D*(phaseReal x y+2*y*Real.pi)+blockError D η
  let Z := -2*Real.pi*(D*y)
  let L := D*((peak:ℝ)/fix)+blockError D η+5*driftCost+4
  have X : P+y+K+Z ≤ L+(-y) := by
    unfold P K Z L
    linear_combination QE+fb+hf
  have M := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr X)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) D0.le) trigpos) (norm_nonneg (edgeDelta n q e)))
  change Real.exp P*(d*(2*(3*D*Real.exp y)*Real.exp K*(bentTrigConstant*Real.exp Z)))≤
    (6*D*bentTrigConstant*Real.exp L)*(d*Real.exp (-y))
  calc _ = (6*D*bentTrigConstant*d)*Real.exp (P+y+K+Z) := by
             rw [Real.exp_add (P+y+K) Z,Real.exp_add (P+y) K,Real.exp_add P y]; ring
       _ ≤ (6*D*bentTrigConstant*d)*Real.exp (L+(-y)) := M
       _ = _ := by rw [Real.exp_add L (-y)]; ring
end OddZetaSix.B40a.Witness
