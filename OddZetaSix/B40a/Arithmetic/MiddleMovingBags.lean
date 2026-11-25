import OddZetaSix.B40a.Arithmetic.MiddleMovingSite
import OddZetaSix.B40a.Arithmetic.MiddleScaling

namespace OddZetaSix.B40a.Cert.Transport
open Set StripGrid
noncomputable section

theorem floor_ratio (s : Scale) (k : ℤ) : ⌊(k:ℝ)/s.ratio⌋=k*s.d/s.p := by
  have hp : (0:ℝ)<s.p := by exact_mod_cast s.hp
  have hd : (0:ℝ)<s.d := by exact_mod_cast s.hd
  have eq : (k:ℝ)/s.ratio=((k:ℝ)*s.d)/s.p := by unfold Scale.ratio; field_simp <;> ring
  let q := k*s.d/s.p
  have low := (Int.le_ediv_iff_mul_le s.hp).mp (le_refl q)
  have high := Int.lt_ediv_add_one_mul_self (k*s.d) s.hp
  rw [eq,Int.floor_eq_iff,le_div_iff₀ hp,div_lt_iff₀ hp]
  exact ⟨by exact_mod_cast low,by exact_mod_cast high⟩

theorem norm_floor {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    (k : ℕ) (hk : k∈middleFrequencies) :
    ((k:ℤ)*(4*s.d))/(4*s.p)=((k:ℤ)*(4*t.d))/(4*t.p) := by
  rw [show (k:ℤ)*(4*s.d)=4*(k*s.d) by ring,show (k:ℤ)*(4*t.d)=4*(k*t.d) by ring,
    Int.mul_ediv_mul_of_pos _ _ (by decide : (0:ℤ)<4),Int.mul_ediv_mul_of_pos _ _ (by decide : (0:ℤ)<4),
    ←floor_ratio,←floor_ratio]
  simpa only [Int.cast_natCast] using (middleRows_floor hr hs hk).trans (middleRows_floor hr ht hk).symm

theorem site_scores {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    (v : Tag×Tag) (hv : v∈tiles s) (neg : Bool) (i : ℤ) :
    middleSite (4*s.p) (4*s.d) (site s v neg i)=middleSite (4*t.p) (4*t.d) (site t v neg i) := by
  have H := sameRow hr s t hs ht
  have f := site_floor H v hv neg i
  have cut (e : ℤ) (he : e∈signedMiddleRadii) :
      (site s v neg i < e*(4*s.d)) ↔ (site t v neg i < e*(4*t.d)) := by
    simpa only [zero_mul,add_zero] using (site_vs_wall H v hv neg i e 0 he).1
  have hneg (s : Scale) : site s v (!neg) (-i) = -site s v neg i := by
    cases neg <;> simp [site] <;> ring
  have plus := site_floor H v hv (!neg) (-i) 34 (by decide)
  simp only [hneg,sub_neg_eq_add] at plus
  have N := norm_floor hr hs ht
  unfold middleSite; dsimp only
  simp only [cut 17 (by decide),cut 16 (by decide),plus,f 25 (by decide),f (-25) (by decide),
    f 17 (by decide),f (-17) (by decide),f 16 (by decide),f (-16) (by decide),f (-34) (by decide),
    f (-59) (by decide),f 59 (by decide), f 34 (by decide),
    show (50:ℤ)*(4*s.d)/(4*s.p)=50*(4*t.d)/(4*t.p) from N 50 (by decide),
    show (34:ℤ)*(4*s.d)/(4*s.p)=34*(4*t.d)/(4*t.p) from N 34 (by decide),
    show (32:ℤ)*(4*s.d)/(4*s.p)=32*(4*t.d)/(4*t.p) from N 32 (by decide),
    show (25:ℤ)*(4*s.d)/(4*s.p)=25*(4*t.d)/(4*t.p) from N 25 (by decide)]

def start (s : Scale) (v : Tag×Tag) (neg : Bool) :=
  if neg then 4*s.p-centerAt s v else centerAt s v
private theorem start_add (s : Scale) (v : Tag×Tag) (neg : Bool) (i : ℤ) :
    start s v neg+i*(4*s.p)=site s v neg (if neg then i+1 else i) := by
  cases neg <;> simp only [start,site,ite_true,ite_false,Bool.false_eq_true] <;> ring

private theorem progression_scores {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    (v : Tag×Tag) (hv : v∈tiles s) (neg : Bool) :
    (iRange (start s v neg) (25*(4*s.d)) (4*s.p)).flatMap (middleSite (4*s.p) (4*s.d)) =
    (iRange (start t v neg) (25*(4*t.d)) (4*t.p)).flatMap (middleSite (4*t.p) (4*t.d)) := by
  let count (z : Scale) := ((25*(4*z.d)-start z v neg+4*z.p-1)/(4*z.p)).toNat
  have pos (z : Scale) : 0<4*z.p := by have := z.hp; omega
  have H := sameRow hr s t hs ht
  have idx (i : ℕ) : i<count s ↔ i<count t := by
    unfold count
    rw [middle_range_index _ _ _ _ (pos s),middle_range_index _ _ _ _ (pos t),start_add,start_add]
    simpa only [zero_mul,add_zero] using (site_vs_wall H v hv neg (if neg then (i:ℤ)+1 else i) 25 0 (by decide)).1
  have hcnt : count s=count t := by have := idx (count s); have := idx (count t); omega
  unfold iRange
  simp only [ite_eq_right (pos s).not_ge,ite_eq_right (pos t).not_ge,List.flatMap_map]
  change (List.range (count s)).flatMap _=(List.range (count t)).flatMap _
  rw [hcnt]; apply List.flatMap_congr
  intro i _
  rw [start_add,start_add]
  exact site_scores hr hs ht v hv _ _

def bag (s : Scale) (v : Tag×Tag) :=
  middleSortedSlots ((middleClassSites (4*s.p) (4*s.d) (centerAt s v)).flatMap
    (middleSite (4*s.p) (4*s.d)))

theorem bag_eq {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    (v : Tag×Tag) (hv : v∈tiles s) : bag s v=bag t v := by
  unfold bag middleClassSites
  apply congrArg middleSortedSlots
  simp only [List.flatMap_append]
  exact congrArg₂ List.append (progression_scores hr hs ht v hv false) (progression_scores hr hs ht v hv true)

theorem classes_moving {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right) :
    middleClasses (4*t.p) (4*t.d) =
      (tiles s).map (fun v=>(loc t v.2-loc t v.1,(bag s v).toArray)) := by
  change ((strips (4*t.p) (4*t.d)).map (fun v => (v.2-v.1,
    (middleSortedSlots ((middleClassSites (4*t.p) (4*t.d) ((v.1+v.2)/2)).flatMap
      (middleSite (4*t.p) (4*t.d)))).toArray))) = _
  rw [tile_list (sameRow hr s t hs ht),List.map_map]
  apply List.map_congr_left; intro v hv
  change (_, (bag t v).toArray)=(_, (bag s v).toArray)
  rw [bag_eq hr hs ht v hv]
  rfl

end
end OddZetaSix.B40a.Cert.Transport
