import OddZetaSix.B40a.Analysis.SignedCircleEnergy
import OddZetaSix.B40a.Analysis.VandermondeContour

noncomputable section
namespace OddZetaSix.B40a
open Finset Filter Real Orbit Matrix
open scoped Topology

theorem orbit_regularized_comm {η : ℝ} (hη : 0<η) (u v : ℂ) (r s : ℝ) :
    orbitEnergy η u v r s=orbitEnergy η v u s r := by
  have H := energy_limit η hη u v r s
  apply tendsto_nhds_unique H
  apply (energy_limit η hη v u s r).congr'
  filter_upwards with n
  simp only [avg,logKernel,←Finset.sum_div]
  congr 2
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [norm_sub_rev]

theorem interaction_comm (u v : ℂ) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    interaction u v r s=interaction v u s r := by
  have H := (interaction_limit v u s r hr).congr'
    (Eventually.of_forall fun n=>(orbit_regularized_comm (eta_pos n) u v r s).symm)
  linarith only [tendsto_nhds_unique (interaction_limit u v r s hs) H]

/-- The signed-energy comparison for positive masses of equal total mass. -/
theorem two_clouds {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι→ℂ) (r a : ι→ℝ) (v : κ→ℂ) (s b : κ→ℝ)
    (hr : ∀ i,0<r i) (hs : ∀ k,0<s k) (hm : ∑ i,a i=∑ k,b k) :
    (∑ i,∑ j,a i*a j*interaction (u i) (u j) (r i) (r j)) +
    (∑ k,∑ l,b k*b l*interaction (v k) (v l) (s k) (s l)) ≤
    2*∑ i,∑ k,a i*b k*interaction (u i) (v k) (r i) (s k) := by
  classical
  let Z := Sum.elim u v
  let R := Sum.elim r s
  let W := Sum.elim a (fun k=> -(b k))
  have hpos (x : ι ⊕ κ) : 0<R x := by cases x with | inl i=>exact hr i | inr k=>exact hs k
  have hsum : ∑ x,W x=0 := by simp [W,Fintype.sum_sum_type,hm]
  have H := signed_circle_energy_nonpos Z R W hpos hsum
  simp only [Z,R,W,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,neg_mul,mul_neg,
    sum_neg_distrib,sum_add_distrib] at H
  have swap : (∑ k,∑ i,b k*a i*interaction (v k) (u i) (s k) (r i)) =
    ∑ i,∑ k,a i*b k*interaction (u i) (v k) (r i) (s k) := by
    rw [sum_comm]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro k _
    rw [interaction_comm _ _ (hs k) (hr i),mul_comm (b k)]
  linarith only [H,swap]

private theorem log_det_sq_eq {h : ℕ} (z : Fin h→ℂ) (hz : Function.Injective z) :
    Real.log ‖(vandermonde z).det^2‖ = ∑ i,∑ j,
        (if i=j then 0 else Real.log ‖z i-z j‖) := by
  classical
  let w (i j : Fin h) := Real.log ‖z j-z i‖
  have ne (i j : Fin h) (hj : j∈Ioi i) : ‖z j-z i‖≠0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h=> (mem_Ioi.mp hj).ne' (hz h)))
  have prodlog (i : Fin h) : Real.log (∏ j ∈ Ioi i,‖z j-z i‖)=∑ j ∈ Ioi i,w i j :=
    Real.log_prod (ne i)
  have hprod : ∀ i∈(univ:Finset (Fin h)), (∏ j ∈ Ioi i,‖z j-z i‖)≠0 := fun i _=>prod_ne_zero_iff.mpr (ne i)
  rw [norm_pow,Real.log_pow,det_vandermonde]
  simp only [Complex.norm_prod]
  rw [Real.log_prod hprod]
  simp_rw [prodlog]
  let g (i j : Fin h) := if i<j then w i j else 0
  have half (i : Fin h) : ∑ j ∈ Ioi i,w i j=∑ j,g i j := by
    rw [←sum_filter]; apply sum_congr _ (fun _ _=>rfl); ext j; simp
  have pair (i j : Fin h) : (if i=j then 0 else Real.log ‖z i-z j‖)=g i j+g j i := by
    rcases lt_trichotomy i j with h|h|h
    · simp [g,w,h,h.ne,not_lt_of_ge h.le,norm_sub_rev (z j) (z i)]
    · subst j; simp [g]
    · simp [g,w,h,h.ne',not_lt_of_ge h.le]
  simp_rw [half,pair,sum_add_distrib]
  rw [sum_comm (f:=fun i j=>g j i)]
  push_cast; ring

/-- Pointwise bound for the squared Vandermonde, valid also at collisions.
Here b gives the *total* witness mass h; no singular diagonal is discarded. -/
theorem vandermonde_witness_bound {h : ℕ} {κ : Type*} [Fintype κ]
    (z : Fin h→ℂ) (v : κ→ℂ) (s b : κ→ℝ)
    (hs : ∀ k,0<s k) (hb : ∀ k,0≤b k) (hm : ∑ k,b k=(h:ℝ)) {ε : ℝ} (hε : 0<ε) :
    ‖(vandermonde z).det^2‖ ≤ Real.exp
      (2*(∑ i,∑ k,b k*(circlePotential (v k) (s k) (z i)+ε/s k))
       -(∑ k,∑ l,b k*b l*interaction (v k) (v l) (s k) (s l))-(h:ℝ)*Real.log ε) := by
  classical
  by_cases hz : Function.Injective z
  · have H := two_clouds z (fun _=>ε) (fun _=>1) v s b (fun _=>hε) hs (by simpa using hm.symm)
    simp only [one_mul] at H
    have HC : (∑ i,∑ k,b k*interaction (z i) (v k) ε (s k)) ≤ _ :=
      sum_le_sum (fun i _=>sum_le_sum (fun k _=>mul_le_mul_of_nonneg_left
        (circlePotential_average_le (v k) (z i) (s k) ε (hs k) hε) (hb k)))
    have L (i j : Fin h) : (if i=j then Real.log ε else Real.log ‖z i-z j‖) ≤ interaction (z i) (z j) ε ε := by
      split
      · rename_i he; subst j; exact (circleSelfEnergy _ _ hε).symm.le
      · rename_i he
        exact circleInteraction_ge_log (z j) (z i) ε ε hε hε (fun H=>he (hz H))
    have splitL (i j : Fin h) : (if i=j then Real.log ε else Real.log ‖z i-z j‖) =
      (if i=j then Real.log ε else 0)+(if i=j then 0 else Real.log ‖z i-z j‖) := by split <;> simp_all
    have LL := sum_le_sum (s:=univ) (fun i _=>sum_le_sum (s:=univ) (fun j _=>L i j))
    simp_rw [splitL,sum_add_distrib] at LL
    simp only [sum_ite_eq,mem_univ,ite_true,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at LL
    have hne := Matrix.det_vandermonde_ne_zero_iff.mpr hz
    apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (pow_ne_zero _ hne))).mp
    rw [log_det_sq_eq z hz]
    linarith only [H,HC,LL]
  · have hzero : (vandermonde z).det=0 := not_ne_iff.mp (fun h=>hz (det_vandermonde_ne_zero_iff.mp h))
    simp only [hzero,zero_pow (by decide : 2≠0),norm_zero]
    exact (Real.exp_pos _).le

end OddZetaSix.B40a
