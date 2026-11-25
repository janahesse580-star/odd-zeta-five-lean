import OddZetaSix.B40a.Analysis.PhaseEndpoints
import OddZetaSix.B40a.Analysis.ClippedChord

noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Filter Set
open scoped Topology

/-- Horizontal coordinate on an affine contour, after translating by a real
block endpoint. The vertical coordinate is t. -/
def lineX (m c t : ℝ) := m*t+c
def lineQ (m c t : ℝ) := (lineX m c t)^2+t^2
def linePrim (m c t : ℝ) := primReal (lineX m c t) t
def lineD (m c t : ℝ) := m/2*Real.log (lineQ m c t)+Real.arctan (lineX m c t/t)
def lineDD (m c t : ℝ) := (lineX m c t*(m^2-1)+2*m*t)/lineQ m c t

private theorem prim_formula (m c t : ℝ) :
    linePrim m c t = lineX m c t/2*Real.log (lineQ m c t)-lineX m c t+t*Real.arctan (lineX m c t/t) := by
  by_cases h : t=0 <;> simp [linePrim,primReal,lineQ,pow_two,h]

private theorem dx (m c t : ℝ) : HasDerivAt (lineX m c) m t := by
  change HasDerivAt (fun x : ℝ => m*x+c) m t
  exact (((hasDerivAt_id t).const_mul m).add_const c).congr_deriv (mul_one m)

private theorem dq (m c t : ℝ) : HasDerivAt (lineQ m c) (2*lineX m c t*m+2*t) t := by
  apply (((dx m c t).pow 2).add ((hasDerivAt_id t).pow 2)).congr_deriv
  simp

private theorem qpos {m c t : ℝ} (ht : t≠0) : 0<lineQ m c t :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ht)

private theorem atan_d (m c t : ℝ) (ht : t≠0) :
    HasDerivAt (fun x=>Real.arctan (lineX m c x/x)) ((m*t-lineX m c t)/lineQ m c t) t := by
  have G : HasDerivAt (fun x => lineX m c x / x) ((m*t-lineX m c t)/t^2) t := by
    apply ((dx m c t).div (hasDerivAt_id t) ht).congr_deriv
    simp
  have H := G.arctan
  apply H.congr_deriv
  unfold lineQ
  field_simp [ht,(qpos (m:=m) (c:=c) ht).ne']
  <;> ring

theorem linePrim_deriv (m c t : ℝ) (ht : t≠0) :
    HasDerivAt (linePrim m c) (lineD m c t) t := by
  have dl := (dq m c t).log (qpos ht).ne'
  have H := ((((dx m c t).div_const 2).mul dl).sub (dx m c t)).add ((hasDerivAt_id t).mul (atan_d m c t ht))
  rw [show linePrim m c=(fun x=>lineX m c x/2*Real.log (lineQ m c x)-lineX m c x+x*Real.arctan (lineX m c x/x))
    from funext (prim_formula m c)]
  apply H.congr_deriv
  simp only [id_eq,one_mul]; unfold lineD
  field_simp [(qpos (m:=m) (c:=c) ht).ne']
  <;> simp [lineQ] <;> ring

theorem lineD_deriv (m c t : ℝ) (ht : t≠0) :
    HasDerivAt (lineD m c) (lineDD m c t) t := by
  have H := (((dq m c t).log (qpos ht).ne').const_mul (m/2)).add (atan_d m c t ht)
  apply H.congr_deriv
  unfold lineDD
  field_simp [(qpos (m:=m) (c:=c) ht).ne']
  <;> ring

private theorem atan_term_zero (m c : ℝ) :
    ContinuousAt (fun t=>t*Real.arctan (lineX m c t/t)) 0 := by
  have hi : Tendsto (fun t : ℝ=>|t| *(π/2)) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.continuousAt (x:=0)).tendsto.mul_const (π/2)
  unfold ContinuousAt
  simp only [zero_mul]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) _ hi
  intro t
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨by linarith only [(Real.neg_pi_div_two_lt_arctan (lineX m c t/t))],
      (Real.arctan_lt_pi_div_two _).le⟩) (abs_nonneg _)

theorem linePrim_cont_at (m c t : ℝ) (hp : 0<lineQ m c t) : ContinuousAt (linePrim m c) t := by
  by_cases ht : t=0
  · subst t
    rw [show linePrim m c=(fun x=>lineX m c x/2*Real.log (lineQ m c x)-lineX m c x+x*Real.arctan (lineX m c x/x))
      from funext (prim_formula m c)]
    exact (((dx m c 0).continuousAt.div_const 2 |>.mul ((dq m c 0).continuousAt.log hp.ne')).sub
      (dx m c 0).continuousAt).add (atan_term_zero m c)
  · exact (linePrim_deriv m c t ht).continuousAt

private theorem dd_bound (m c t : ℝ) {d : ℝ} (hd : 0<d) (h : d^2≤lineQ m c t) :
    |lineDD m c t|≤(1+m^2)/d := by
  let x := lineX m c t
  let v := x*(m^2-1)+2*m*t
  have hQ : 0<lineQ m c t := (sq_pos_of_pos hd).trans_le h
  have ident : (1+m^2)^2*(x^2+t^2)-v^2=(2*m*x-(m^2-1)*t)^2 := by unfold v; ring
  have hv : |v|≤(1+m^2)*Real.sqrt (lineQ m c t) := by
    have hs := Real.sq_sqrt hQ.le
    have hr : 0≤(1+m^2)*Real.sqrt (lineQ m c t) := by positivity
    apply le_of_sq_le_sq _ hr
    rw [sq_abs,mul_pow,hs]
    change v^2≤(1+m^2)^2*(x^2+t^2)
    linarith only [ident,sq_nonneg (2*m*x-(m^2-1)*t)]
  have hsd := (Real.le_sqrt hd.le hQ.le).mpr h
  change |v/lineQ m c t|≤_
  rw [abs_div,abs_of_pos hQ]
  apply (div_le_div_iff₀ hQ hd).mpr
  calc |v| *d ≤ ((1+m^2)*Real.sqrt (lineQ m c t))*Real.sqrt (lineQ m c t) :=
         mul_le_mul hv hsd hd.le (by positivity)
       _ = _ := by rw [mul_assoc,←sq,Real.sq_sqrt hQ.le]

/-- Chord convexity for a signed endpoint contribution on one affine panel.
The lower distance controls both rising and falling blocks and is valid at
the bottom endpoint, where arctan(x/y) itself need not be continuous. -/
theorem signed_phase_convex (m c a b w d : ℝ) (ha : 0≤a) (hd : 0<d)
    (hl : ∀ t∈Icc a b,d^2≤lineQ m c t) :
    ConvexOn ℝ (Icc a b) (fun t=>w*linePrim m c t+(|w| *(1+m^2)/d)*t^2/2) := by
  apply convexOn_quadratic_of_lower_curvature
    (df:=fun t=>w*lineD m c t) (ddf:=fun t=>w*lineDD m c t)
  · intro t ht
    exact (continuousAt_const.mul (linePrim_cont_at m c t ((sq_pos_of_pos hd).trans_le (hl t ht)))).continuousWithinAt
  · intro t ht; exact (linePrim_deriv m c t (ha.trans_lt ht.1).ne').const_mul _
  · intro t ht; exact (lineD_deriv m c t (ha.trans_lt ht.1).ne').const_mul _
  · intro t ht
    have H := dd_bound m c t hd (hl t ⟨ht.1.le,ht.2.le⟩)
    have hh := mul_le_mul_of_nonneg_left H (abs_nonneg w)
    rw [←abs_mul,←mul_div_assoc] at hh
    exact (abs_le.mp hh).1
end OddZetaSix.B40a.Cert
