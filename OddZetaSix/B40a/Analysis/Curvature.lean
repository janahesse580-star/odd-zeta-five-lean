import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OddZetaSix.B40a

open Set Filter
open scoped Topology

theorem chord_curvature {f : ℝ → ℝ} {K a b y : ℝ} (hK : 0 ≤ K)
    (hf : ConvexOn ℝ (Icc a b) (fun x => f x + K*x^2/2))
    (hy : y ∈ Icc a b) :
    f y ≤ max (f a) (f b) + K*(b-a)^2/8 := by
  obtain hab | rfl := (hy.1.trans hy.2).lt_or_eq
  · let u : ℝ := (b-y)/(b-a)
    let v : ℝ := (y-a)/(b-a)
    have hud : u*(b-a) = b-y := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
    have hvd : v*(b-a) = y-a := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
    have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hab.le)
    have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hab.le)
    have huv : u+v=1 := by
      apply (mul_right_cancel₀ (sub_ne_zero.mpr hab.ne'))
      nlinarith [hud,hvd]
    have hxy : u*a+v*b=y := by nlinarith [hvd,congrArg (fun x : ℝ => x*a) huv]
    have h := hf.2 (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hu hv huv
    simp only [smul_eq_mul] at h
    rw [hxy] at h
    have hvar : u*a^2+v*b^2-y^2 = (y-a)*(b-y) := by
      linear_combination
        (a+b)*hxy - a*b*huv
    have h1 : u*(f a) + v*(f b) ≤ max (f a) (f b) := by
      calc
        _ ≤ u * max (f a) (f b) + v * max (f a) (f b) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hv)
        _ = _ := by rw [← add_mul, huv, one_mul]
    have h2 : K*(y-a)*(b-y)/2 ≤ K*(b-a)^2/8 := by
      have hh := mul_nonneg hK (sq_nonneg (2*y-a-b))
      nlinarith only [hh]
    nlinarith only [h,h1,h2,congrArg (fun x : ℝ => K*x/2) hvar]
  · have hya : y = a := le_antisymm hy.2 hy.1
    simp [hya]

private theorem slope_middle {f : ℝ → ℝ} {x c z : ℝ} (hxc : x<c) (hcz : c<z)
    (h : (f c-f x)/(c-x) ≤ (f z-f c)/(z-c)) :
    (f c-f x)/(c-x) ≤ (f z-f x)/(z-x) ∧
      (f z-f x)/(z-x) ≤ (f z-f c)/(z-c) := by
  have hxc' : 0<c-x := sub_pos.2 hxc
  have hcz' : 0<z-c := sub_pos.2 hcz
  have hxz' : 0<z-x := sub_pos.2 (hxc.trans hcz)
  have hh := (div_le_div_iff₀ hxc' hcz').1 h
  constructor
  · apply (div_le_div_iff₀ hxc' hxz').2
    nlinarith only [hh]
  · apply (div_le_div_iff₀ hxz' hcz').2
    nlinarith only [hh]

/-- Gluing using the two one-sided derivatives. No second derivative at the join is needed. -/
theorem convexOn_glue {f : ℝ → ℝ} {a c b L R : ℝ}
    (hl : ConvexOn ℝ (Icc a c) f) (hr : ConvexOn ℝ (Icc c b) f)
    (hL : HasDerivWithinAt f L (Iio c) c) (hR : HasDerivWithinAt f R (Ioi c) c)
    (hLR : L ≤ R) : ConvexOn ℝ (Icc a b) f := by
  have cross (x z : ℝ) (hax : a ≤ x) (hzb : z ≤ b) (hxc : x<c) (hcz : c<z) :
      (f c - f x)/(c-x) ≤ (f z-f c)/(z-c) := by
    simpa [slope_def_field] using (hl.slope_le_of_hasDerivWithinAt_Iio ⟨hax,hxc.le⟩ ⟨hax.trans hxc.le,le_rfl⟩
      hxc hL).trans (hLR.trans (hr.le_slope_of_hasDerivWithinAt_Ioi
        ⟨le_rfl,hcz.le.trans hzb⟩ ⟨hcz.le,hzb⟩ hcz hR))
  apply convexOn_of_slope_mono_adjacent (convex_Icc _ _)
  intro x y z hx hz hxy hyz
  by_cases hzc : z ≤ c
  · exact hl.slope_mono_adjacent ⟨hx.1,(hxy.trans hyz).le.trans hzc⟩ ⟨hz.1,hzc⟩ hxy hyz
  by_cases hcx : c ≤ x
  · exact hr.slope_mono_adjacent ⟨hcx,hx.2⟩ ⟨hcx.trans (hxy.trans hyz).le,hz.2⟩ hxy hyz
  have hxc : x<c := lt_of_not_ge hcx
  have hcz : c<z := lt_of_not_ge hzc
  rcases lt_trichotomy y c with hyc | rfl | hcy
  · have hleft := hl.slope_mono_adjacent ⟨hx.1,hxc.le⟩ ⟨hx.1.trans hxc.le,le_rfl⟩ hxy hyc
    exact hleft.trans (slope_middle hyc hcz (cross y z (hx.1.trans hxy.le) hz.2 hyc hcz)).1
  · exact cross x z hx.1 hz.2 hxc hcz
  · have hright := hr.slope_mono_adjacent ⟨le_rfl,hcz.le.trans hz.2⟩ ⟨hcz.le,hz.2⟩ hcy hyz
    exact (slope_middle hxc hcy (cross x y hx.1 (hyz.le.trans hz.2) hxc hcy)).2.trans hright

/-- At contact, dominance of the left branch on a left neighbourhood implies the
required upward order of the branch derivatives. -/
theorem contact_derivative_order {l r : ℝ → ℝ} {c L R : ℝ}
    (hl : HasDerivAt l L c) (hr : HasDerivAt r R c) (he : l c = r c)
    (hdom : ∀ᶠ x in 𝓝[<] c, r x ≤ l x) : L ≤ R := by
  have hd := (hl.sub hr).tendsto_slope.mono_left (nhdsLT_le_nhdsNE c)
  have hle : L-R ≤ 0 := by
    apply le_of_tendsto hd
    filter_upwards [hdom, self_mem_nhdsWithin] with x hx hxc
    have hxc' : x<c := hxc
    simp only [slope, vsub_eq_sub, smul_eq_mul, Pi.sub_apply, sub_self, he, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr (sub_nonpos.mpr hxc'.le)) (sub_nonneg.mpr hx)
  linarith


/-- At a branch switch of a maximum, the derivative of the chosen left branch is
at most that of the chosen right branch. This applies when the maximum is not differentiable. -/
theorem convexOn_max_switch {l r : ℝ → ℝ} {a c b L R : ℝ}
    (hac : a<c) (hcb : c<b)
    (hl : ConvexOn ℝ (Icc a c) l) (hr : ConvexOn ℝ (Icc c b) r)
    (hdl : HasDerivAt l L c) (hdr : HasDerivAt r R c) (he : l c = r c)
    (hlDom : ∀ x ∈ Icc a c, r x ≤ l x) (hrDom : ∀ x ∈ Icc c b, l x ≤ r x) :
    ConvexOn ℝ (Icc a b) (fun x => max (l x) (r x)) := by
  have hleft : ∀ᶠ x in 𝓝[<] c, r x ≤ l x := by
    filter_upwards [Ioo_mem_nhdsLT hac] with x hx
    exact hlDom x ⟨hx.1.le,hx.2.le⟩
  have hright : ∀ᶠ x in 𝓝[>] c, l x ≤ r x := by
    filter_upwards [Ioo_mem_nhdsGT hcb] with x hx
    exact hrDom x ⟨hx.1.le,hx.2.le⟩
  refine convexOn_glue (hl.congr ?_) (hr.congr ?_) ?_ ?_
    (contact_derivative_order hdl hdr he hleft)
  · intro x hx
    exact (max_eq_left (hlDom x hx)).symm
  · intro x hx
    exact (max_eq_right (hrDom x hx)).symm
  · apply hdl.hasDerivWithinAt.congr_of_eventuallyEq
    · exact hleft.mono fun _ h => max_eq_left h
    · rw [he,max_self]
  · apply hdr.hasDerivWithinAt.congr_of_eventuallyEq
    · exact hright.mono fun _ h => max_eq_right h
    · rw [he,max_self]

/-- One crossing of a circle, for the outside-to-inside orientation. The convex
outside bound and the smooth branch derivatives are independent inputs. -/
theorem clippedLog_enter {w : ℝ → ℂ} {u : ℂ} {r a c b K L : ℝ}
    (hr : 0<r) (hac : a<c) (hcb : c<b) (hK : 0≤K)
    (hAt : ‖w c-u‖ = r)
    (hOut : ∀ y ∈ Icc a c, r ≤ ‖w y-u‖)
    (hIn : ∀ y ∈ Icc c b, 0 < ‖w y-u‖ ∧ ‖w y-u‖ ≤ r)
    (hc : ConvexOn ℝ (Icc a c) (fun y => Real.log ‖w y-u‖ + K*y^2/2))
    (hd : HasDerivAt (fun y => Real.log ‖w y-u‖ + K*y^2/2) L c) :
    ConvexOn ℝ (Icc a b) (fun y => Real.log (max r ‖w y-u‖) + K*y^2/2) := by
  let left : ℝ → ℝ := fun y => Real.log ‖w y-u‖ + K*y^2/2
  let right : ℝ → ℝ := fun y => Real.log r + K*y^2/2
  have hcRight : ConvexOn ℝ (Icc c b) right := by
    have hcSq := ((show Even 2 from by decide).convexOn_pow (𝕜 := ℝ)).subset
      (Set.subset_univ (Icc c b)) (convex_Icc c b)
    have hc' := (hcSq.smul (show 0 ≤ K/2 by positivity)).add_const (Real.log r)
    apply hc'.congr
    intro y _
    simp only [right, Pi.add_apply, smul_eq_mul]
    ring
  have hright : HasDerivAt right ((K/2)*(2*c)) c := by
    have h := (((hasDerivAt_id c).pow 2).const_mul (K/2)).const_add (Real.log r)
    have hf : right = (fun x : ℝ => Real.log r + (K/2)*(id^2) x) := by
      funext x
      simp only [right, Pi.pow_apply, id_eq]
      ring
    rw [hf]
    simpa only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] using h
  have hc' := convexOn_max_switch hac hcb hc hcRight hd hright
    (show left c = right c by simp [left,right,hAt])
    (fun y hy => by dsimp [left,right]; linarith [Real.log_le_log hr (hOut y hy)])
    (fun y hy => by dsimp [left,right]; linarith [Real.log_le_log (hIn y hy).1 (hIn y hy).2])
  apply hc'.congr
  intro y hy
  change max (left y) (right y) = Real.log (max r ‖w y-u‖) + K*y^2/2
  by_cases hh : y ≤ c
  · have ho := hOut y ⟨hy.1,hh⟩
    have hlr : right y ≤ left y := by dsimp [left,right]; linarith [Real.log_le_log hr ho]
    rw [max_eq_left hlr,max_eq_right ho]
  · have hi := hIn y ⟨le_of_not_ge hh,hy.2⟩
    have hlr : left y ≤ right y := by dsimp [left,right]; linarith [Real.log_le_log hi.1 hi.2]
    rw [max_eq_right hlr,max_eq_left hi.2]


/-- The smooth pieces only need two derivatives on their open interiors.
This is the interface used with the algebraic estimate on a circle's outside arc. -/
theorem convexOn_quadratic_of_lower_curvature
    {f df ddf : ℝ → ℝ} {a b K : ℝ}
    (hcontinuity : ContinuousOn f (Icc a b))
    (hdf : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hddf : ∀ x ∈ Ioo a b, HasDerivAt df (ddf x) x)
    (hddf_lower : ∀ x ∈ Ioo a b, -K ≤ ddf x) :
    ConvexOn ℝ (Icc a b) (fun x => f x + K*x^2/2) := by
  have hfirst (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun t => f t + K*t^2/2) (df x + K*x) x := by
    have hq := (((hasDerivAt_id x).pow 2).const_mul (K/2))
    have hq' : HasDerivAt (fun t : ℝ => K*t^2/2) (K*x) x := by
      have hfun : (fun t : ℝ => K*t^2/2) = (fun t => K/2*(id^2) t) := by
        funext t
        simp only [Pi.pow_apply,id_eq]
        ring
      rw [hfun]
      have he : K / 2 * ((↑(2 : ℕ) : ℝ) * id x ^ (2-1 : ℕ)*1) = K*x := by
        norm_num
        ring
      rw [← he]
      exact hq
    exact (hdf x hx).add hq'
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f' := fun x => df x+K*x) (f'' := fun x => ddf x+K)
  · exact hcontinuity.add (by fun_prop)
  · intro x hx
    rw [interior_Icc] at hx
    exact (hfirst x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hlinear : HasDerivAt (fun y : ℝ => K*y) K x := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul K)
    have hsum : HasDerivAt (fun y => df y+K*y) (ddf x+K) x := (hddf x hx).add hlinear
    exact hsum.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have := hddf_lower x hx
    linarith

end OddZetaSix.B40a
