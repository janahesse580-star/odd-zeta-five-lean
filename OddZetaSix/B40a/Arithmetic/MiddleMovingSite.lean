import OddZetaSix.B40a.Arithmetic.MiddleRowStrips
import OddZetaSix.B40a.Arithmetic.MiddleFoldWalls

namespace OddZetaSix.B40a.Cert.Transport
open Set StripGrid
noncomputable section

def tiles (s : Scale) := adjacent (ordered s)
def endpoints (t : Scale) (v : Tag×Tag) := (loc t v.1,loc t v.2)
def centerAt (t : Scale) (v : Tag×Tag) := (loc t v.1+loc t v.2)/2

theorem adjacent_map {α β : Type} (f : α→β) (l : List α) :
    adjacent (l.map f)=(adjacent l).map (fun v=>(f v.1,f v.2)) := by
  induction l with
  | nil => rfl
  | cons a xs ih => cases xs with
    | nil => rfl
    | cons b ys => exact congrArg (List.cons (f a,f b)) ih

theorem tile_list {s t : Scale} (H : SameRow s t) :
    strips (4*t.p) (4*t.d)=(tiles s).map (endpoints t) := by
  unfold strips; rw [←ordered_walls H,adjacent_map]; rfl

private theorem tag_is_wall (s : Scale) (z : Tag) (h₁ : 0≤loc s z) (h₂ : loc s z≤2*s.p) :
    loc s z∈walls (4*s.p) (4*s.d) := by
  obtain ⟨l,hl⟩ := z
  cases l with
  | half =>
    apply ((increasing_spec _).2.2 _).mpr
    apply List.mem_cons_of_mem
    change 2*s.p∈4*s.p/2 :: _
    rw [show 4*s.p/2=2*s.p by omega]; exact List.mem_cons_self
  | regular e i =>
    let x := 4*(e*s.d+i*s.p)
    change 0≤x at h₁; change x≤2*s.p at h₂
    change x∈walls _ _
    have hp := s.hp
    have he : foldAddr (4*s.p) (e*(4*s.d))=x := by
      have hmod : x%(4*s.p)=(e*(4*s.d))%(4*s.p) := by
        rw [show x=e*(4*s.d)+i*(4*s.p) by dsimp [x]; ring,Int.add_mul_emod_self_right]
      rw [Int.emod_eq_of_lt h₁ (by omega)] at hmod
      unfold foldAddr; rw [←hmod]; omega
    apply ((increasing_spec _).2.2 _).mpr
    rcases lt_trichotomy e 0 with hn|rfl|hh
    · have hm : -e∈radii := by
        change e∈signedMiddleRadii at hl
        simp only [radii,signedMiddleRadii,List.mem_cons,List.not_mem_nil,or_false] at hl ⊢
        omega
      apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨-e,hm,?_⟩))
      rw [neg_mul]
      exact (middleFoldWall_neg (4*s.p) (e*(4*s.d)) (by omega)).trans he
    · have hz : x=0 := by simpa [foldAddr,hp.le] using he.symm
      rw [hz]; exact List.mem_cons_self
    · have hm : e∈radii := by
        change e∈signedMiddleRadii at hl
        simp only [radii,signedMiddleRadii,List.mem_cons,List.not_mem_nil,or_false] at hl ⊢; omega
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,hm,he⟩))

private theorem midpoint_side {s t : Scale} (H : SameRow s t) (v : Tag×Tag) (hv : v∈tiles s) (l : Tag) :
    (loc t l<centerAt t v ↔ loc t l≤loc t v.1) ∧
    (centerAt t v<loc t l ↔ loc t v.2≤loc t l) ∧ loc t l≠centerAt t v := by
  have he : endpoints t v ∈ strips (4*t.p) (4*t.d) := (tile_list H) ▸ List.mem_map.mpr ⟨v,hv,rfl⟩
  obtain ⟨h0,hab,hh,_,h₁,h₂⟩ := strip_window _ _ _ _ t.hp he
  have hgap := (adjacent_gap _ (increasing_spec _).1 he).2.2.2
  change loc t v.1<centerAt t v at h₁
  change centerAt t v<loc t v.2 at h₂
  have hsep : ¬(loc t v.1<loc t l ∧ loc t l<loc t v.2) := by
    intro ha; exact hgap _ (tag_is_wall _ _ (h0.trans ha.1.le) (ha.2.le.trans hh)) ha
  omega

/-- The sign of each wall relative to the actual integer midpoint survives
every ratio change inside a certified row, including the half-period cells. -/
theorem midpoint_order {s t : Scale} (H : SameRow s t) (v : Tag×Tag) (hv : v∈tiles s) (l : Tag) :
    (loc s l<centerAt s v ↔ loc t l<centerAt t v) ∧
    (centerAt s v<loc s l ↔ centerAt t v<loc t l) := by
  have hs := midpoint_side (SameRow.refl s) v hv l
  have ht := midpoint_side H v hv l
  exact ⟨hs.1.trans ((H.le _ _).trans ht.1.symm),hs.2.1.trans ((H.le _ _).trans ht.2.1.symm)⟩

def site (s : Scale) (v : Tag×Tag) (neg : Bool) (i : ℤ) :=
  (if neg then -centerAt s v else centerAt s v) + i*(4*s.p)

theorem site_vs_wall {s t : Scale} (H : SameRow s t) (v : Tag×Tag) (hv : v∈tiles s)
    (neg : Bool) (i e k : ℤ) (he : e∈signedMiddleRadii) :
    (site s v neg i < e*(4*s.d)+k*(4*s.p) ↔ site t v neg i < e*(4*t.d)+k*(4*t.p)) ∧
    (e*(4*s.d)+k*(4*s.p) < site s v neg i ↔ e*(4*t.d)+k*(4*t.p) < site t v neg i) := by
  cases neg with
  | false =>
    have h := midpoint_order H v hv (regular e (k-i) he)
    change (4*(e*s.d+(k-i)*s.p)<centerAt s v ↔ 4*(e*t.d+(k-i)*t.p)<centerAt t v) ∧
      (centerAt s v<4*(e*s.d+(k-i)*s.p) ↔ centerAt t v<4*(e*t.d+(k-i)*t.p)) at h
    simp only [site,Bool.false_eq_true,ite_false]
    constructor <;> constructor <;> intro hh
    · have := h.2.mp (by linarith only [hh]); linarith
    · have := h.2.mpr (by linarith only [hh]); linarith
    · have := h.1.mp (by linarith only [hh]); linarith
    · have := h.1.mpr (by linarith only [hh]); linarith
  | true =>
    have h := midpoint_order H v hv (regular (-e) (i-k) (negRadius he))
    change (4*((-e)*s.d+(i-k)*s.p)<centerAt s v ↔ 4*((-e)*t.d+(i-k)*t.p)<centerAt t v) ∧
      (centerAt s v<4*((-e)*s.d+(i-k)*s.p) ↔ centerAt t v<4*((-e)*t.d+(i-k)*t.p)) at h
    simp only [site,ite_true]
    constructor <;> constructor <;> intro hh
    · have := h.1.mp (by linarith only [hh]); linarith
    · have := h.1.mpr (by linarith only [hh]); linarith
    · have := h.2.mp (by linarith only [hh]); linarith
    · have := h.2.mpr (by linarith only [hh]); linarith

theorem site_floor {s t : Scale} (H : SameRow s t) (v : Tag×Tag) (hv : v∈tiles s)
    (neg : Bool) (i e : ℤ) (he : e∈signedMiddleRadii) :
    (e*(4*s.d)-site s v neg i)/(4*s.p)=(e*(4*t.d)-site t v neg i)/(4*t.p) := by
  have comp (z : ℤ) : z≤(e*(4*s.d)-site s v neg i)/(4*s.p) ↔ z≤(e*(4*t.d)-site t v neg i)/(4*t.p) := by
    rw [Int.le_ediv_iff_mul_le (by have := s.hp; omega),Int.le_ediv_iff_mul_le (by have := t.hp; omega)]
    have hh := not_congr (site_vs_wall H v hv neg i e (-z) he).2
    simp only [not_lt,neg_mul] at hh
    constructor <;> intro h
    · have := hh.mp (by omega); omega
    · have := hh.mpr (by omega); omega
  exact le_antisymm ((comp _).mp le_rfl) ((comp _).mpr le_rfl)

end
end OddZetaSix.B40a.Cert.Transport
