import OddZetaSix.B40a.Analysis.CertifiedField
import OddZetaSix.B40a.Analysis.Coordinates
noncomputable section
namespace OddZetaSix.B40a.Witness
open Set Cert Cert.Chord
def nodeX (i : Fin 8) := 118/100-bendC i
def nextNode (e : Fin 8) (h : e.val<7) : Fin 8 := ⟨e.val+1,by omega⟩
def stopX (e : Fin 8) := if h : e.val<7 then nodeX (nextNode e h) else nodeX 7
def stopY (n : ℕ) (q : ℝ) (e : Fin 8) :=
  if h : e.val<7 then bendHeight (nextNode e h) else q/scaleN n
def edgeX (e : Fin 8) (t : ℝ) := lerp t (nodeX e) (stopX e)
def edgeY (n : ℕ) (q : ℝ) (e : Fin 8) (t : ℝ) := lerp t (bendHeight e) (stopY n q e)

theorem scaled_node (n : ℕ) (hn : 0<n) (s : Bool) (k : Fin 8) :
    (bendNode n s k).re+OddZetaSix.B40a.center n=scaleN n*(nodeX k+anchorDrift n) ∧
    (bendNode n s k).im=contourSide s*(scaleN n*bendHeight k) := by
  have D : 0<scaleN n := by unfold scaleN; positivity
  have H := (div_eq_iff D.ne').mp (scaled_node_real n hn k)
  exact ⟨by simpa [bendNode,nodeX,mul_comm] using H,by simp [bendNode,scaleN,bendNodeY]⟩

theorem scaled_stop (n : ℕ) (hn : 0<n) (q : ℝ) (e : BendEdge) :
    (edgeStop n q e).re+OddZetaSix.B40a.center n=scaleN n*(stopX e.2+anchorDrift n) ∧
    (edgeStop n q e).im=contourSide e.1*(scaleN n*stopY n q e.2) := by
  have D : 0<scaleN n := by unfold scaleN; positivity
  unfold edgeStop stopX stopY
  split_ifs with h
  · exact scaled_node n hn e.1 (nextNode e.2 h)
  · have A := (scaled_node n hn e.1 7).1
    exact ⟨by simpa [bendNode] using A, by rw [pointAt_im]; congr 1; field_simp⟩

theorem edge_affine (n : ℕ) (hn : 0<n) (q : ℝ) (e : BendEdge) (t : ℝ) :
    let z := edgePoint n q (e,t)
    z.re+(OddZetaSix.B40a.center n:ℝ)=scaleN n*(edgeX e.2 t+anchorDrift n) ∧
    z.im=contourSide e.1*(scaleN n*edgeY n q e.2 t) := by
  obtain ⟨A,B⟩ := scaled_node n hn e.1 e.2
  obtain ⟨G,H⟩ := scaled_stop n hn q e
  dsimp only
  simp only [edgePoint,edgeDelta,edgeStart,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,add_zero,Complex.sub_re,Complex.sub_im]
  unfold edgeX edgeY lerp
  constructor
  · linear_combination (1-t)*A+t*G
  · linear_combination (1-t)*B+t*H

theorem nodeX_bounds (e : Fin 8) : 1≤nodeX e ∧ nodeX e≤2 := by
  fin_cases e <;> norm_num [nodeX,bendC,Matrix.cons_val_zero,Matrix.cons_val_succ]
theorem nodeY_bounds (e : Fin 8) : 0≤bendHeight e ∧ bendHeight e≤1 := by
  fin_cases e <;> norm_num [bendHeight,Matrix.cons_val_zero,Matrix.cons_val_succ]
private theorem lerp_bounds {a b t : ℝ} (ht : t∈Icc 0 1) (hab : a≤b) :
    a≤lerp t a b ∧ lerp t a b≤b := by
  unfold lerp; constructor <;> nlinarith only [mul_nonneg ht.1 (sub_nonneg.mpr hab),mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]
theorem increasing (e : Fin 8) (h : e.val<7) : bendHeight e≤bendHeight (nextNode e h) := by
  fin_cases e <;> norm_num [nextNode,bendHeight,Matrix.cons_val_zero,Matrix.cons_val_succ] at *

theorem edgeY_range (n : ℕ) (hn : 0<n) (q : ℝ) (hq : bendNodeY n 7≤q) (e : Fin 8) {t : ℝ} (ht : t∈Icc 0 1) :
    bendHeight e≤edgeY n q e t ∧ edgeY n q e t≤stopY n q e := by
  apply lerp_bounds ht
  unfold stopY
  split_ifs with h
  · exact increasing e h
  · have E : e=7 := Fin.ext (by have := e.isLt; change e.val=7; omega)
    rw [E]; apply (le_div_iff₀ (by unfold scaleN; positivity)).mpr
    simpa [bendNodeY,scaleN,mul_comm] using hq

theorem edge_coordinates (n : ℕ) (hn : 0<n) (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge)
    {t : ℝ} (ht : t∈Icc 0 1) :
    Coordinates n (edgePoint n q (e,t)) (edgeX e.2 t) (edgeY n q e.2 t) (anchorDrift n) := by
  obtain ⟨A,B⟩ := edge_affine n hn q e t
  have D : 0<scaleN n := by unfold scaleN; positivity
  have y0 := (nodeY_bounds e.2).1.trans (edgeY_range n hn q hq e.2 ht).1
  have im : |(edgePoint n q (e,t)).im|=scaleN n*edgeY n q e.2 t := by
    rw [B,abs_mul,abs_of_nonneg (mul_nonneg D.le y0)]
    rcases e with ⟨s,k⟩; cases s <;> simp [contourSide]
  have sx : 1≤stopX e.2 ∧ stopX e.2≤2 := by unfold stopX; split_ifs <;> exact nodeX_bounds _
  have nx := nodeX_bounds e.2
  have H0 := add_le_add (mul_le_mul_of_nonneg_left nx.1 (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left sx.1 ht.1)
  have H1 := add_le_add (mul_le_mul_of_nonneg_left nx.2 (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left sx.2 ht.1)
  obtain ⟨d0,d1⟩ := anchorDrift_bounds n hn
  refine ⟨?_,im,?_,?_,y0,d0,?_⟩
  · unfold scaleN at A ⊢; unfold OddZetaSix.B40a.center at A; push_cast at A; linarith only [A]
  · unfold edgeX lerp; linarith only [H0]
  · unfold edgeX lerp; linarith only [H1]
  · apply d1.trans; unfold scaleN; apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [Nat.cast_nonneg (α:=ℝ) n]

theorem edge_square (n : ℕ) (hn : 0<n) (q : ℝ) (e : BendEdge) (t : ℝ) :
    bendScaledSquare n q (e,t)=(pointAt e.1 (edgeX e.2 t) (edgeY n q e.2 t)+(anchorDrift n:ℂ))^2 := by
  obtain ⟨A,B⟩ := edge_affine n hn q e t
  unfold bendScaledSquare
  congr 1
  apply (div_eq_iff (by exact mul_ne_zero (by norm_num) (by exact_mod_cast hn.ne') : (50*(n:ℂ))≠0)).mpr
  apply Complex.ext
  · simp [Complex.mul_re,Complex.add_re,scaleN] at A ⊢
    linarith only [A]
  · simp [Complex.mul_im,Complex.add_im,scaleN] at B ⊢
    linarith only [B]

end OddZetaSix.B40a.Witness

namespace OddZetaSix.B40a.Witness
open Set Cert Cert.Chord
def bandOf : Fin 8 → Band := ![((0,1700),(2500,2200)),((2500,2200),(5000,1000)),
  ((5000,1000),(10000,-2000)),((10000,-2000),(20000,-8100)),
  ((20000,-8100),(35000,-16300)),((35000,-16300),(55000,-25700)),
  ((55000,-25700),(85000,-45500)),((85000,-45500),(400000,-45500))]

private theorem band_values (j : Fin 8) :
    let e := bandOf j
    let B := if h : j.val<7 then bendHeight (nextNode j h) else 4
    e∈bands ∧ (e.1.1:ℝ)/(phaseTicks:ℝ)=bendHeight j ∧ (e.2.1:ℝ)/(phaseTicks:ℝ)=B ∧
    (slope e:ℝ)*bendHeight j+offset e=nodeX j ∧ (slope e:ℝ)*B+offset e=stopX j := by
  fin_cases j <;> norm_num [bandOf,bands,adjacent,knots,Chord.slope,offset,baseX,nodeX,stopX,bendC,
    nextNode,bendHeight,phaseTicks,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> change 327/200=59/50-(-(91/200):ℝ) <;> norm_num

theorem edge_field_bound (n : ℕ) (hn : 0<n) (q : ℝ) (hq : bendNodeY n 7≤q) (e : BendEdge)
    {t : ℝ} (ht : t∈Icc 0 1) :
    let y := edgeY n q e.2 t
    limitingField e.1 (edgeX e.2 t) y ≤ (peak:ℝ)/fix-6*max (y-4) 0 := by
  let j := e.2
  let y := edgeY n q j t
  have hy := edgeY_range n hn q hq j ht
  have V := band_values j
  dsimp only at V
  obtain ⟨he,ha,hb,hx,hu⟩ := V
  by_cases h : j.val<7
  · simp only [dite_eq_left h] at hb hu
    have E : edgeX j t=(slope (bandOf j):ℝ)*y+offset (bandOf j) := by
      change lerp t (nodeX j) (stopX j) = (Chord.slope (bandOf j):ℝ)*lerp t (bendHeight j) (stopY n q j)+offset (bandOf j)
      simp only [lerp,stopY,dite_eq_left h]
      linear_combination (1-t)*(-hx)+t*(-hu)
    have U : y≤bendHeight (nextNode j h) := by simpa [y,stopY,h] using hy.2
    have M : max (y-4) 0=0 := max_eq_right (by linarith only [U,(nodeY_bounds (nextNode j h)).2])
    change limitingField e.1 (edgeX j t) y≤(peak:ℝ)/fix-6*max (y-4) 0
    rw [E,M,mul_zero,sub_zero]
    exact band_field_bound e.1 he (ha ▸ hy.1) (hb ▸ U)
  · have jj : j=7 := Fin.ext (by have := j.isLt; change j.val=7; omega)
    have X : edgeX j t=327/200 := by
      have Q : nodeX 7=327/200 := by change 118/100-(-455/1000:ℝ)=_; norm_num
      rw [jj]; change lerp t (nodeX 7) (nodeX 7)=_; rw [Q]; unfold lerp; ring
    change limitingField e.1 (edgeX j t) y≤(peak:ℝ)/fix-6*max (y-4) 0
    rw [X]
    by_cases H : 4≤y
    · rw [max_eq_left (sub_nonneg.mpr H)]
      exact tail_field_bound _ _ H
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge H)),mul_zero,sub_zero]
      simp only [dite_eq_right h] at hb
      have E : (slope (bandOf j):ℝ)*y+offset (bandOf j)=327/200 := by
        rw [jj]; change ((Chord.slope ((85000,-45500),(400000,-45500)):ℚ):ℝ)*y+((offset ((85000,-45500),(400000,-45500)):ℚ):ℝ)=_; norm_num [Chord.slope,offset,baseX,phaseTicks]
      rw [←E]; exact band_field_bound _ he (ha ▸ hy.1) (hb ▸ le_of_not_ge H)
end OddZetaSix.B40a.Witness
