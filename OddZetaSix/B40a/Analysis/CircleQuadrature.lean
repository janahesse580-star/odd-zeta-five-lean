import OddZetaSix.B40a.Analysis.CirclePotential
import OddZetaSix.B40a.Analysis.RegularizedEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
namespace OddZetaSix.B40a.Orbit
open Finset Filter Set MeasureTheory
open scoped Topology

def grid (n k : ℕ) : ℝ := (k:ℝ)/n
def avg (n : ℕ) (f : ℝ→ℝ) := (∑ i : Fin n,f (grid n i))/n

theorem innerContinuous (f : ℝ×ℝ→ℝ) (hf : Continuous f) :
    Continuous (fun x : ℝ=>∫ y in (0:ℝ)..1,f (x,y)) := by
  have H := continuous_parametric_integral_of_continuous (μ:=volume)
    (f:=fun x y : ℝ=>f (x,y)) hf (isCompact_Icc (a:=(0:ℝ)) (b:=1))
  simpa only [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc] using H

private theorem grid_cell {n k : ℕ} (hn : 0<n) (hk : k<n) :
    0≤grid n k ∧ grid n k≤grid n (k+1) ∧ grid n (k+1)≤1 ∧
    grid n (k+1)-grid n k=1/(n:ℝ) := by
  have hd : (0:ℝ)<n := by exact_mod_cast hn
  unfold grid; push_cast
  exact ⟨by positivity,div_le_div_of_nonneg_right (by linarith) hd.le,
    (div_le_one hd).mpr (by exact_mod_cast hk),by ring⟩

private theorem integral_le_mesh {n : ℕ} (hn : 0<n) (f : ℝ→ℝ) (hf : Continuous f)
    (g : ℕ→ℝ) (ht : ∀ k<n,∀ x∈Icc (grid n k) (grid n (k+1)),f x≤g k) :
    (∫ x in (0:ℝ)..1,f x)≤(∑ k ∈ range n,g k)/n := by
  have hd : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have eq := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (n:=n) (a:=grid n)
    (fun k _=>hf.intervalIntegrable (grid n k) (grid n (k+1)))
  rw [show grid n 0=0 by simp [grid],show grid n n=1 by simp [grid,hd]] at eq
  rw [←eq,Finset.sum_div]
  apply sum_le_sum
  intro k hk
  obtain ⟨_,hab,_,hw⟩ := grid_cell hn (mem_range.mp hk)
  have H := intervalIntegral.integral_mono_on hab (hf.intervalIntegrable (μ:=volume) _ _)
    (intervalIntegrable_const (c:=g k)) (ht k (mem_range.mp hk))
  simpa only [intervalIntegral.integral_const,smul_eq_mul,hw,one_div,div_eq_inv_mul,mul_one] using H

theorem mesh_error {n : ℕ} (hn : 0<n) (f : ℝ→ℝ) (hf : Continuous f) (ε : ℝ)
    (he : ∀ k<n,∀ x∈Icc (grid n k) (grid n (k+1)),|f x-f (grid n k)|≤ε) :
    |(∫ x in (0:ℝ)..1,f x)-avg n f|≤ε := by
  have hp : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have H := integral_le_mesh hn f hf (fun k=>f (grid n k)+ε)
    (fun k hk x hx=>by have := (abs_le.mp (he k hk x hx)).2; linarith)
  have L := integral_le_mesh hn (fun x=> -(f x)) hf.neg (fun k=> -(f (grid n k))+ε)
    (fun k hk x hx=>by have := (abs_le.mp (he k hk x hx)).1; linarith)
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,sum_neg_distrib,add_div,
    mul_div_cancel_left₀ _ hp,intervalIntegral.integral_neg,neg_div] at H L
  unfold avg
  rw [Fin.sum_univ_eq_sum_range (fun k=>f (grid n k))]
  apply abs_le.mpr
  constructor <;> linarith

private theorem mesh_mem {n k : ℕ} (hn : 0<n) (hk : k<n) : grid n k∈Icc (0:ℝ) 1 := by
  obtain ⟨h,l,u,_⟩ := grid_cell hn hk
  exact ⟨h,l.trans u⟩

/-- Tensor-product polygon quadrature for a continuous kernel. Both polygon
orders tend to infinity along the same sequence, including for self-energy. -/
theorem double_tendsto (f : ℝ×ℝ→ℝ) (hf : Continuous f) :
    Tendsto (fun n : ℕ=>avg n (fun x=>avg n (fun y=>f (x,y)))) atTop
      (𝓝 (∫ x in (0:ℝ)..1,∫ y in (0:ℝ)..1,f (x,y))) := by
  let S := Icc (0:ℝ) 1
  have hu := (isCompact_Icc.prod isCompact_Icc : IsCompact (S ×ˢ S)).uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε/3) (by positivity)
  have hinv : ∀ᶠ n : ℕ in atTop,1/(n:ℝ)<δ := by
    exact (tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ))
  filter_upwards [hinv,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have osc {k : ℕ} (hk : k<n) {x : ℝ} (hx : x∈Icc (grid n k) (grid n (k+1))) :
      x∈S ∧ dist x (grid n k)<δ := by
    obtain ⟨l,m,u,w⟩ := grid_cell hn0 hk
    exact ⟨⟨l.trans hx.1,hx.2.trans u⟩,by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hx.1)]; linarith [hx.2]⟩
  let F := fun x : ℝ=>∫ y in (0:ℝ)..1,f (x,y)
  have inner (x : ℝ) (hx : x∈S) :
      |F x-avg n (fun y=>f (x,y))|≤ε/3 := by
    apply mesh_error hn0 _ (hf.comp (continuous_const.prodMk continuous_id)) _
    intro k hk y hy
    have o := osc hk hy
    have H := hmod _ (show (x,y)∈S ×ˢ S from ⟨hx,o.1⟩)
      _ (show (x,grid n k)∈S ×ˢ S from ⟨hx,mesh_mem hn0 hk⟩) (by simpa using o.2)
    exact H.le
  have outer := mesh_error hn0 F (innerContinuous f hf) (ε/3) (by
    intro k hk x hx
    obtain ⟨hxS,hd⟩ := osc hk hx
    have variation (y : ℝ) (hy : y∈S) : |f (x,y)-f (grid n k,y)|≤ε/3 :=
      (hmod _ (show (x,y)∈S ×ˢ S from ⟨hxS,hy⟩)
        _ (show (grid n k,y)∈S ×ˢ S from ⟨mesh_mem hn0 hk,hy⟩) (by simpa using hd)).le
    have ci (u : ℝ) : IntervalIntegrable (fun v=>f (u,v)) volume 0 1 := (hf.comp (continuous_const.prodMk continuous_id) : Continuous (fun v : ℝ=>f (u,v))).intervalIntegrable (μ:=volume) 0 1
    unfold F
    rw [←intervalIntegral.integral_sub (ci x) (ci (grid n k)),←Real.norm_eq_abs]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
      (C:=ε/3) (f:=fun y=>f (x,y)-f (grid n k,y)) (fun y hy=>by
        apply variation; rw [uIoc_of_le zero_le_one] at hy; exact ⟨hy.1.le,hy.2⟩)
    simpa using H)
  have innerSum : |avg n F-avg n (fun x=>avg n (fun y=>f (x,y)))|≤ε/3 := by
    have hN : (0:ℝ)<n := by exact_mod_cast hn0
    unfold avg
    rw [←sub_div,abs_div,abs_of_pos hN,div_le_iff₀ hN,←sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _i : Fin n,(ε/3) := sum_le_sum (fun i _=>inner _ (mesh_mem hn0 i.isLt))
         _ = _ := by simp; ring
  rw [Real.dist_eq,abs_sub_comm]
  calc
    _ ≤ |(∫ x in (0:ℝ)..1,F x)-avg n F|+|avg n F-avg n (fun x=>avg n (fun y=>f (x,y)))| :=
      abs_sub_le _ _ _
    _ < _ := by linarith

end OddZetaSix.B40a.Orbit
