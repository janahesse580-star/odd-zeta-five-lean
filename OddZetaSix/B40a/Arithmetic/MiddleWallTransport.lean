import OddZetaSix.B40a.Arithmetic.MiddleWallOrder
import OddZetaSix.B40a.Arithmetic.MiddleStripGrid

namespace OddZetaSix.B40a.Cert.Transport
open Set StripGrid
noncomputable section

/-- Coordinates at the fourfold integer scale used by middleValue. -/
structure Scale where
  p : ℤ
  d : ℤ
  hp : 0<p
  hd : 0<d

def Scale.ratio (s : Scale) : ℝ := (s.p:ℝ)/s.d
theorem Scale.pos (s : Scale) : 0<s.ratio := div_pos (by exact_mod_cast s.hp) (by exact_mod_cast s.hd)

inductive Wall where
  | regular (e i : ℤ)
  | half
  deriving DecidableEq

def Wall.valid : Wall→Prop
  | .regular e _ => e∈signedMiddleRadii
  | .half => True

def Wall.pos (s : Scale) : Wall → ℤ
  | .regular e i => 4*(e*s.d+i*s.p)
  | .half => 2*s.p

def Wall.val (P : ℝ) : Wall→ℝ
  | .regular e i => (e:ℝ)+(i:ℝ)*P
  | .half => P/2

theorem Wall.scaled (s : Scale) (l : Wall) :
    ((l.pos s):ℝ) = 4*(s.d:ℝ)*l.val s.ratio := by
  have hd : (s.d:ℝ)≠0 := by exact_mod_cast s.hd.ne'
  cases l <;> simp only [Wall.pos,Wall.val,Scale.ratio,Int.cast_mul,Int.cast_add,Int.cast_ofNat]
    <;> field_simp <;> ring

private theorem half_freq : signedMiddleRadii.all (fun e=> decide
    (e≠0 → (2*e).natAbs∈middleFrequencies))=true := by decide +kernel
private theorem gap_freq : signedMiddleRadii.all (fun e=>signedMiddleRadii.all (fun f =>
    decide (e≠f → (e-f).natAbs∈middleFrequencies)))=true := by decide +kernel

private theorem ratio_cmp {r : ArithRow} (hr : r∈middleRows) {P Q : ℝ}
    (hP : P∈Ioo (r.left:ℝ) r.right) (hQ : Q∈Ioo (r.left:ℝ) r.right)
    (hp : 0<P) (hq : 0<Q) (k b : ℤ) (hk : k≠0 → k.natAbs∈middleFrequencies) :
    ((k:ℝ)<b*P ↔ (k:ℝ)<b*Q) ∧ ((b:ℝ)*P<k ↔ (b:ℝ)*Q<k) := by
  by_cases hz : k=0
  · subst k
    rw [Int.cast_zero]
    have HH (z : ℝ) (hz : 0<z) : (0<(b:ℝ)*z ↔ 0<(b:ℝ)) ∧ ((b:ℝ)*z<0 ↔ (b:ℝ)<0) := by
      constructor
      · exact mul_pos_iff_of_pos_right hz
      · constructor
        · intro h; by_contra! h'; exact (not_lt_of_ge (mul_nonneg h' hz.le)) h
        · intro h; exact mul_neg_of_neg_of_pos h hz
    exact ⟨(HH P hp).1.trans (HH Q hq).1.symm,(HH P hp).2.trans (HH Q hq).2.symm⟩
  let a := k.natAbs
  have H (x : ℝ) (hx : x∈Ioo (r.left:ℝ) r.right) (hx0 : 0<x) (z : ℤ) :
      ((a:ℝ)<z*x ↔ middleFloor r a<z) ∧ ((z:ℝ)*x<a ↔ z≤middleFloor r a) := by
    have hf := middleRows_floor hr hx (hk hz)
    have hs := middle_floor_strict hr hx (hk hz)
    change ⌊(a:ℝ)/x⌋=middleFloor r a at hf
    change (middleFloor r a:ℝ)<(a:ℝ)/x at hs
    refine ⟨?_,?_⟩
    · rw [←div_lt_iff₀ hx0,←hf,Int.floor_lt]
    · rw [←lt_div_iff₀ hx0]
      exact ⟨fun h=> hf ▸ Int.le_floor.mpr h.le, fun h=>(by exact_mod_cast h : (z:ℝ)≤middleFloor r a).trans_lt hs⟩
  by_cases h0 : 0≤k
  · have he : (a:ℝ)=(k:ℝ) := by
      have hz : (a:ℤ)=k := Int.natAbs_of_nonneg h0
      exact_mod_cast hz
    have h1 := H P hP hp b; have h2 := H Q hQ hq b
    rw [he] at h1 h2
    exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩
  · have he : (a:ℝ)=-(k:ℝ) := by
      have hz : (a:ℤ) = -k := by dsimp [a]; rw [←Int.natAbs_neg,Int.natAbs_of_nonneg (by omega)]
      exact_mod_cast hz
    have h1 := H P hP hp (-b); have h2 := H Q hQ hq (-b)
    simp only [he,Int.cast_neg,neg_mul,neg_lt_neg_iff] at h1 h2
    exact ⟨h1.2.trans h2.2.symm,h1.1.trans h2.1.symm⟩

/-- Uniform order for all signed translates AND the half-period wall, with
no exception where the latter switches its position in a certificate row. -/
theorem wall_order {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    {u v : Wall} (hu : u.valid) (hv : v.valid) : u.pos s<v.pos s ↔ u.pos t<v.pos t := by
  have H (s : Scale) : u.pos s<v.pos s ↔ u.val s.ratio<v.val s.ratio := by
    rw [←Int.cast_lt (R:=ℝ),Wall.scaled,Wall.scaled,mul_lt_mul_iff_right₀
      (show 0<4*(s.d:ℝ) by exact mul_pos (by norm_num) (by exact_mod_cast s.hd))]
  rw [H,H]; clear H
  cases u with
  | half =>
    cases v with
    | half => simp
    | regular e i =>
      have hk := of_decide_eq_true (List.all_eq_true.mp half_freq e hv)
      have h := (ratio_cmp hr hs ht s.pos t.pos (2*e) (1-2*i) (by intro h; exact hk (by omega))).2
      simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_one,Int.cast_sub] at h
      simpa only [Wall.val] using (show s.ratio/2<(e:ℝ)+i*s.ratio ↔ t.ratio/2<(e:ℝ)+i*t.ratio by
        constructor <;> intro H
        · have := h.mp (by linarith only [H] : (1-2*(i:ℝ))*s.ratio<2*e); linarith
        · have := h.mpr (by linarith only [H] : (1-2*(i:ℝ))*t.ratio<2*e); linarith)
  | regular e i =>
    cases v with
    | half =>
      have hk := of_decide_eq_true (List.all_eq_true.mp half_freq e hu)
      have h := (ratio_cmp hr hs ht s.pos t.pos (2*e) (1-2*i) (by intro h; exact hk (by omega))).1
      simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_one,Int.cast_sub] at h
      change (e:ℝ)+i*s.ratio<s.ratio/2 ↔ (e:ℝ)+i*t.ratio<t.ratio/2
      constructor <;> intro H
      · have := h.mp (by linarith only [H] : 2*(e:ℝ)<(1-2*i)*s.ratio); linarith
      · have := h.mpr (by linarith only [H] : 2*(e:ℝ)<(1-2*i)*t.ratio); linarith
    | regular f j =>
      have hk := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp gap_freq e hu) f hv)
      have h := (ratio_cmp hr hs ht s.pos t.pos (e-f) (j-i) (by intro h; exact hk (by omega))).1
      simp only [Int.cast_sub,sub_mul] at h
      change (e:ℝ)+i*s.ratio<f+j*s.ratio ↔ (e:ℝ)+i*t.ratio<f+j*t.ratio
      constructor <;> intro H
      · have := h.mp (by linarith); linarith
      · have := h.mpr (by linarith); linarith

end
end OddZetaSix.B40a.Cert.Transport
