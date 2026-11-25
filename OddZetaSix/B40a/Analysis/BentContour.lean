import OddZetaSix.B40a.Analysis.BendGeometry

/-! Deform the actual B40a vertical residue contour to the certified polygonal contour.
Each half lies in its own open convex domain, sharing the half-integer crossing. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

def straightSegment (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, f (a+(t : ℂ)*(b-a))*(b-a)

theorem segment_point_mem {D : Set ℂ} (hD : Convex ℝ D) {a b : ℂ}
    (ha : a ∈ D) (hb : b ∈ D) (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    a+(t : ℂ)*(b-a) ∈ D := by
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  have h := hD ha hb (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
  change (1-t) • a+t • b ∈ D at h
  convert h using 1
  simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

private theorem straightSegment_primitive {D : Set ℂ} (hD : Convex ℝ D) {F f : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hf : ContinuousOn f D)
    {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) :
    straightSegment f a b = F b-F a := by
  let g : ℝ → ℂ := fun t => a+(t : ℂ)*(b-a)
  have hmem : MapsTo g (uIcc (0:ℝ) 1) D := fun t ht => segment_point_mem hD ha hb t ht
  have hg : Continuous g := by unfold g; fun_prop
  have hi : IntervalIntegrable (fun t => f (g t)*(b-a)) volume 0 1 :=
    ((hf.comp hg.continuousOn hmem).mul continuousOn_const).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) : HasDerivAt (F ∘ g) (f (g t)*(b-a)) t := by
    simpa only [Function.comp_def,g,id_eq,one_mul] using
      ((hF (g t) (hmem ht)).comp (t : ℂ)
        (((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a)).comp_ofReal
  simpa [straightSegment,g,Function.comp_def] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi)

def sideDirection (s : Bool) : ℂ := (contourSide s : ℂ)*Complex.I

def directedLine (f : ℂ → ℂ) (s : Bool) (x lo hi : ℝ) : ℂ :=
  ∫ y in lo..hi, f (pointAt s x y)*sideDirection s

private theorem directedLine_primitive {D : Set ℂ} {F f : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hf : ContinuousOn f D)
    (s : Bool) (x a b : ℝ) (hmem : MapsTo (pointAt s x) (uIcc a b) D) :
    directedLine f s x a b = F (pointAt s x b)-F (pointAt s x a) := by
  have he (y : ℝ) : pointAt s x y = (x : ℂ)+(y : ℂ)*sideDirection s := by
    simp only [pointAt,sideDirection,Complex.ofReal_mul]; ring
  have hg : Continuous (pointAt s x) := by
    rw [funext he]
    fun_prop
  have hi : IntervalIntegrable (fun y => f (pointAt s x y)*sideDirection s) volume a b :=
    ((hf.comp hg.continuousOn hmem).mul continuousOn_const).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun y => F (pointAt s x y)) (f (pointAt s x t)*sideDirection s) t := by
    have hpt := hF _ (hmem ht)
    simp only [he] at hpt ⊢
    simpa only [Function.comp_def,id_eq,one_mul] using
      (hpt.comp (t : ℂ)
        (((hasDerivAt_id (t : ℂ)).mul_const (sideDirection s)).const_add (x : ℂ))).comp_ofReal
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

def outwardPolygon (f : ℂ → ℂ) (n : ℕ) (s : Bool) (q : ℝ) : ℂ :=
  (∑ a : Fin 7, straightSegment f (bendNode n s a.castSucc) (bendNode n s a.succ)) +
    directedLine f s (bendNodeX n 7) (bendNodeY n 7) q

def bentTruncation (n i j : ℕ) (q : ℝ) : ℂ :=
  outwardPolygon (contourIntegrand n i j) n true q-
    outwardPolygon (contourIntegrand n i j) n false q

theorem bend_continuousOn (n i j : ℕ) (s : Bool) :
    ContinuousOn (contourIntegrand n i j) (bendDomain n s) := by
  intro z hz
  exact (contourIntegrand_analyticAt n i j z hz.1 (sin_ne_zero_on_bendDomain n s z hz)).continuousAt.continuousWithinAt

/-- Express the finite vertical tail as an affine edge in the same domain. -/
theorem bend_tail_eq_segment (n i j : ℕ) (s : Bool) (q : ℝ) (hq : bendNodeY n 7 ≤ q) :
    directedLine (contourIntegrand n i j) s (bendNodeX n 7) (bendNodeY n 7) q =
      straightSegment (contourIntegrand n i j) (bendNode n s 7) (pointAt s (bendNodeX n 7) q) := by
  obtain ⟨F,hF⟩ := exists_bend_primitive n i j s
  have hc := bend_continuousOn n i j s
  have hm : MapsTo (pointAt s (bendNodeX n 7)) (uIcc (bendNodeY n 7) q) (bendDomain n s) := by
    intro y hy
    rw [uIcc_of_le hq] at hy
    exact pointAt_mem_bendDomain n s _ _ (bendNode_x_in_halfplane n 7)
      ((bendNode_offset_le n 7).trans (by linarith [hy.1]))
  rw [directedLine_primitive hF hc s _ _ _ hm,
    straightSegment_primitive (convex_bendDomain n s) hF hc (bendNode_mem n s 7) (hm right_mem_uIcc)]
  rfl

private theorem polygonDifference (n i j : ℕ) (s : Bool) (q : ℝ) (hq : bendNodeY n 7 ≤ q) :
    outwardPolygon (contourIntegrand n i j) n s q =
      directedLine (contourIntegrand n i j) s (contourAbscissa n) 0 q +
        straightSegment (contourIntegrand n i j)
          (pointAt s (contourAbscissa n) q) (pointAt s (bendNodeX n 7) q) := by
  let f := contourIntegrand n i j
  let D := bendDomain n s
  obtain ⟨F,hF⟩ := exists_bend_primitive n i j s
  have hc := bend_continuousOn n i j s
  have hq0 : 0 ≤ q := (bendNode_height_nonneg n 7).trans hq
  have hmemA : MapsTo (pointAt s (contourAbscissa n)) (uIcc 0 q) D := by
    intro y hy
    rw [uIcc_of_le hq0] at hy
    apply pointAt_mem_bendDomain n s _ _ (contourAbscissa_in_halfplane n)
    have hh := hy.1
    simp; linarith
  have hmemB : MapsTo (pointAt s (bendNodeX n 7)) (uIcc (bendNodeY n 7) q) D := by
    intro y hy
    rw [uIcc_of_le hq] at hy
    apply pointAt_mem_bendDomain n s _ _ (bendNode_x_in_halfplane n 7)
    exact (bendNode_offset_le n 7).trans (by linarith [hy.1])
  have hlinks (a : Fin 7) :
      straightSegment f (bendNode n s a.castSucc) (bendNode n s a.succ) =
        F (bendNode n s a.succ)-F (bendNode n s a.castSucc) :=
    straightSegment_primitive (convex_bendDomain n s) hF hc (bendNode_mem n s _) (bendNode_mem n s _)
  have htel (g : Fin 8 → ℂ) :
      (∑ a : Fin 7, (g a.succ-g a.castSucc)) = g 7-g 0 := by
    let u : ℕ → ℂ := fun a => g (Fin.ofNat 8 a)
    have h := Finset.sum_range_sub u 7
    rw [← Fin.sum_univ_eq_sum_range] at h
    calc
      _ = ∑ a : Fin 7, (u (a.val+1)-u a.val) := by
        apply Finset.sum_congr rfl
        intro a _
        have h₁ : Fin.ofNat 8 (a.val+1) = a.succ := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (show a.val+1<8 by omega)]
        have h₂ : Fin.ofNat 8 a.val = a.castSucc := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (show a.val<8 by omega)]
        simp only [u,h₁,h₂]
      _ = _ := h
  have hH := straightSegment_primitive (convex_bendDomain n s) hF hc
    (hmemA right_mem_uIcc) (hmemB right_mem_uIcc)
  have hVA := directedLine_primitive hF hc s (contourAbscissa n) 0 q hmemA
  have hVB := directedLine_primitive hF hc s (bendNodeX n 7) (bendNodeY n 7) q hmemB
  unfold outwardPolygon
  change (∑ a : Fin 7, straightSegment f (bendNode n s a.castSucc) (bendNode n s a.succ)) +
    directedLine f s (bendNodeX n 7) (bendNodeY n 7) q = _
  simp_rw [hlinks]
  rw [htel (fun a => F (bendNode n s a)),hVA,hVB,hH,bendNode_zero]
  have h0 : pointAt s (contourAbscissa n) 0 = contourPoint n 0 := by simp [pointAt,contourPoint]
  rw [h0]
  change F (pointAt s (bendNodeX n 7) (bendNodeY n 7)) - _ + (_ - _) = _
  ring

theorem verticalTruncation_eq_directed (n : ℕ) (i j : Fin (fiveRank n)) (q : ℝ) :
    verticalTruncation n i j q =
      directedLine (contourIntegrand n i j) true (contourAbscissa n) 0 q-
        directedLine (contourIntegrand n i j) false (contourAbscissa n) 0 q := by
  let G := verticalIntegrand n i j
  have hi (a b : ℝ) : IntervalIntegrable G volume a b := (verticalIntegrand_integrable n i j).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals (f := G) (hi (-q) 0) (hi 0 q)
  have hp : directedLine (contourIntegrand n i j) true (contourAbscissa n) 0 q =
      ∫ y in 0..q, G y := by simp [directedLine,G,verticalIntegrand,sideDirection,pointAt,contourPoint,contourSide]
  have hm : directedLine (contourIntegrand n i j) false (contourAbscissa n) 0 q =
      -(∫ y in -q..0, G y) := by
    unfold directedLine
    have h (y : ℝ) : contourIntegrand n i j (pointAt false (contourAbscissa n) y) * sideDirection false =
        -G (-y) := by simp [sideDirection,pointAt,contourSide,G,verticalIntegrand,contourPoint]
    simp_rw [h]
    rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_neg,neg_zero]
  rw [hp,hm,sub_neg_eq_add,add_comm,hadd]
  rfl

private theorem topLink_tendsto_zero (n : ℕ) (i j : Fin (fiveRank n)) (s : Bool) :
    Tendsto (fun q : ℕ => straightSegment (contourIntegrand n i j)
      (pointAt s (contourAbscissa n) q) (pointAt s (bendNodeX n 7) q)) atTop (𝓝 0) := by
  let C := contourIntegrandDecayConstant n * |bendNodeX n 7-contourAbscissa n|
  apply squeeze_zero_norm' (a := fun q : ℕ => C/(q : ℝ)^(90*n+15))
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (contourDecayRadius n))] with q hq
    have hq2 : (2 : ℝ) ≤ q := (contourDecayRadius_ge_two n).trans hq
    have hbnd : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖contourIntegrand n i j
          (pointAt s (contourAbscissa n) q +
            (t : ℂ)*(pointAt s (bendNodeX n 7) q - pointAt s (contourAbscissa n) q)) *
          (pointAt s (bendNodeX n 7) q - pointAt s (contourAbscissa n) q)‖ ≤
          C/(q : ℝ)^(90*n+15) := by
      intro t _
      let a := pointAt s (contourAbscissa n) q
      let b := pointAt s (bendNodeX n 7) q
      let z := a+(t : ℂ)*(b-a)
      have hd : b-a = ((bendNodeX n 7-contourAbscissa n : ℝ) : ℂ) := by
        simp only [b,a,pointAt,Complex.ofReal_sub]; ring
      have him : z.im = contourSide s*(q : ℝ) := by simp [z,hd,a]
      have habs : |z.im| = (q : ℝ) := by
        rw [him,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ q from Nat.cast_nonneg _)]
        cases s <;> norm_num [contourSide]
      have hnorm : (q : ℝ) ≤ ‖z‖ := habs ▸ (Complex.abs_im_le_norm z)
      have hsin : 1 ≤ ‖Complex.sin ((Real.pi : ℂ)*z)‖ :=
        six_sin_norm_ge_one_of_im z (by rw [habs]; linarith)
      have hdec := contourIntegrand_norm_le_decay n i j z (hq.trans hnorm) hsin
      have hpow : (q : ℝ)^(90*n+15) ≤ ‖z‖^(90*n+15) :=
        pow_le_pow_left₀ (Nat.cast_nonneg q) hnorm _
      have hD := (div_le_div_of_nonneg_left (contourIntegrandDecayConstant_pos n).le
        (pow_pos (by linarith) _) hpow)
      change ‖contourIntegrand n i j z*(b-a)‖ ≤ C/(q : ℝ)^(90*n+15)
      rw [norm_mul,hd,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (hdec.trans hD) (abs_nonneg _)).trans_eq (by unfold C; ring)
    simpa only [straightSegment,sub_zero,abs_one,mul_one] using
      (intervalIntegral.norm_integral_le_of_norm_le_const hbnd)
  · exact (tendsto_const_div_pow C _ (by omega)).comp tendsto_natCast_atTop_atTop

/-- Exact improper integral identity on the prescribed corrected eight-node contour. -/
theorem bentContour_eq_functional (n : ℕ) (i j : Fin (fiveRank n)) :
    Tendsto (fun q : ℕ => bentTruncation n i j q) atTop
      (𝓝 (-(2*(Real.pi : ℂ)*Complex.I)*(fiveFunctional n i j : ℂ))) := by
  have hV : Tendsto (fun q : ℕ => verticalTruncation n i j q) atTop
      (𝓝 (verticalIntegral n i j)) := by
    simpa only [verticalIntegral,verticalTruncation,Function.comp_apply] using
      intervalIntegral_tendsto_integral (verticalIntegrand_integrable n i j)
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hu := topLink_tendsto_zero n i j true
  have hl := topLink_tendsto_zero n i j false
  have he : (fun q : ℕ => bentTruncation n i j q) =ᶠ[atTop]
    (fun q : ℕ => verticalTruncation n i j q +
      straightSegment (contourIntegrand n i j) (pointAt true (contourAbscissa n) q)
        (pointAt true (bendNodeX n 7) q) -
      straightSegment (contourIntegrand n i j) (pointAt false (contourAbscissa n) q)
        (pointAt false (bendNodeX n 7) q)) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (bendNodeY n 7))] with q hq
    rw [bentTruncation,polygonDifference n i j true q hq,polygonDifference n i j false q hq,
      verticalTruncation_eq_directed]
    ring
  rw [← verticalIntegral_eq_functional]
  simpa only [add_zero,sub_zero] using (((hV.add hu).sub hl).congr' he.symm)

end OddZetaSix.B40a
