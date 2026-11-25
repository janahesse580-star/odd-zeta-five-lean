import OddZetaSix.B40a.Arithmetic.MiddleWallTransport

namespace OddZetaSix.B40a.Cert.Transport
open Set StripGrid
noncomputable section

abbrev Tag := {l : Wall // l.valid}
def regular (e i : ℤ) (he : e∈signedMiddleRadii) : Tag := ⟨.regular e i,he⟩
def zeroTag := regular 0 0 (by decide)
def halfTag : Tag := ⟨.half,trivial⟩
def loc (s : Scale) (v : Tag) := v.val.pos s

structure SameRow (s t : Scale) : Prop where
  order : ∀ a b : Tag,loc s a<loc s b ↔ loc t a<loc t b

theorem sameRow {r : ArithRow} (hr : r∈middleRows) (s t : Scale)
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right) :
    SameRow s t := ⟨fun a b=>wall_order hr hs ht a.property b.property⟩

theorem SameRow.le {s t : Scale} (H : SameRow s t) (a b : Tag) :
    loc s a≤loc s b ↔ loc t a≤loc t b := by simpa only [not_lt] using not_congr (H.order b a)

theorem SameRow.eq {s t : Scale} (H : SameRow s t) (a b : Tag) :
    loc s a=loc s b ↔ loc t a=loc t b := by rw [le_antisymm_iff,le_antisymm_iff,H.le,H.le]

theorem SameRow.symm {s t : Scale} (H : SameRow s t) : SameRow t s := ⟨fun a b=>(H.order a b).symm⟩
theorem SameRow.refl (s : Scale) : SameRow s s := ⟨fun _ _=>Iff.rfl⟩

theorem negRadius {e : ℤ} (h : e∈signedMiddleRadii) : -e∈signedMiddleRadii := by
  simp only [signedMiddleRadii,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega

theorem signed_ediv_transport {s t : Scale} (H : SameRow s t) (e : ℤ) (he : e∈signedMiddleRadii) :
    e*s.d/s.p=e*t.d/t.p := by
  let k := e*s.d/s.p
  have hl := (Int.le_ediv_iff_mul_le s.hp).mp (le_refl k)
  have hu := Int.lt_ediv_add_one_mul_self (e*s.d) s.hp
  change e*s.d<(k+1)*s.p at hu
  have h1 := (H.le (regular 0 k (by decide)) (regular e 0 he)).mp (by
    change 4*(0*s.d+k*s.p)≤4*(e*s.d+0*s.p); simp only [zero_mul,zero_add,add_zero]; omega)
  have h2 := (H.order (regular e 0 he) (regular 0 (k+1) (by decide))).mp (by
    change 4*(e*s.d+0*s.p)<4*(0*s.d+(k+1)*s.p); simp only [zero_mul,zero_add,add_zero]; omega)
  change 4*(0*t.d+k*t.p)≤4*(e*t.d+0*t.p) at h1
  change 4*(e*t.d+0*t.p)<4*(0*t.d+(k+1)*t.p) at h2
  simp only [zero_mul,zero_add,add_zero] at h1 h2
  change k=e*t.d/t.p
  exact le_antisymm ((Int.le_ediv_iff_mul_le t.hp).mpr (by omega))
    (by have hh := (Int.ediv_lt_iff_lt_mul t.hp).mpr (by omega : e*t.d<(k+1)*t.p); omega)

def foldedTag (s : Scale) (e : ℤ) (he : e∈signedMiddleRadii) : Tag :=
  let k := e*s.d/s.p
  let a := regular e (-k) he
  if loc s a≤loc s halfTag then a else regular (-e) (k+1) (negRadius he)

theorem foldedTag_eq {s t : Scale} (H : SameRow s t) (e : ℤ) (he : e∈signedMiddleRadii) :
    foldedTag s e he=foldedTag t e he := by
  unfold foldedTag
  simp only [signed_ediv_transport H e he,H.le]

theorem loc_foldedTag (s : Scale) (e : ℤ) (he : e∈signedMiddleRadii) :
    loc s (foldedTag s e he)=foldAddr (4*s.p) (e*(4*s.d)) := by
  rw [show e*(4*s.d)=4*(e*s.d) by ring,foldAddr_scale_four]
  unfold foldedTag foldAddr
  let k := e*s.d/s.p
  have h := Int.emod_add_mul_ediv (e*s.d) s.p
  change (e*s.d)%s.p+s.p*k=e*s.d at h
  rw [mul_comm s.p k] at h
  have hpos : loc s (regular e (-k) he)=4*(e*s.d%s.p) := by
    change 4*(e*s.d+ -k*s.p)=_; rw [neg_mul]; omega
  have hneg : loc s (regular (-e) (k+1) (negRadius he))=4*(s.p-e*s.d%s.p) := by
    change 4*((-e)*s.d+(k+1)*s.p)=_; rw [neg_mul,add_mul,one_mul]; omega
  change loc s (if loc s (regular e (-k) he)≤2*s.p then _ else _)=_
  split_ifs with hh
  · rw [hpos] at hh ⊢; omega
  · rw [hpos] at hh; rw [hneg]; omega

def radii : List ℤ := [16,17,25,34,59]
theorem radius_valid (e : ℤ) (h : e∈radii) : e∈signedMiddleRadii := by
  simp only [radii,signedMiddleRadii,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega

def unsorted (s : Scale) : List Tag :=
  zeroTag::halfTag::radii.attach.map (fun e=>foldedTag s e.val (radius_valid _ e.property))

def ins (s : Scale) (v : Tag) : List Tag → List Tag
  | [] => [v]
  | u::us => if loc s v<loc s u then v::u::us else if loc s v=loc s u then u::us else u::ins s v us
def ordered (s : Scale) := (unsorted s).foldl (fun us v=>ins s v us) []

private theorem loc_ins {s t : Scale} (H : SameRow s t) (v : Tag) (xs : List Tag) :
    (ins s v xs).map (loc t)=insertZ (loc t v) (xs.map (loc t)) := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    simp only [ins,List.map_cons,insertZ,H.order,H.eq]
    split_ifs <;> simp_all

private theorem loc_sort {s t : Scale} (H : SameRow s t) (xs acc : List Tag) :
    (xs.foldl (fun us v=>ins s v us) acc).map (loc t) =
    (xs.map (loc t)).foldl (fun us v=>insertZ v us) (acc.map (loc t)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons,List.map_cons,ih,loc_ins H]

theorem ordered_walls {s t : Scale} (H : SameRow s t) :
    (ordered s).map (loc t)=walls (4*t.p) (4*t.d) := by
  rw [ordered,loc_sort H]
  unfold walls increasingZ unsorted
  simp only [List.map_cons,List.map_nil,List.map_map,Function.comp_def,foldedTag_eq H,loc_foldedTag]
  have hm : (radii.attach.map (fun x=>foldAddr (4*t.p) (x.val*(4*t.d)))) =
    radii.map (fun x=>foldAddr (4*t.p) (x*(4*t.d))) := List.attach_map_val (l:=radii) (f:=fun x : ℤ => foldAddr (4*t.p) (x*(4*t.d)))
  rw [hm]
  simp only [zeroTag,regular,loc,halfTag,Wall.pos,zero_mul,zero_add,mul_zero,radii,show 4*t.p/2=2*t.p by omega]
  rfl

end
end OddZetaSix.B40a.Cert.Transport
