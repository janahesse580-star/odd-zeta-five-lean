import OddZetaSix.B40a.Arithmetic.MiddleMovingBags
import OddZetaSix.B40a.Arithmetic.MiddleDiscreteValue
import OddZetaSix.B40a.Arithmetic.MiddleCapMean

noncomputable section
namespace OddZetaSix.B40a.Cert.Transport
open Set Finset Sweep

def coeff : Wall → ℝ × ℝ
  | .regular e i => (i,e)
  | .half => (1/2,0)

theorem coeff_val (w : Wall) (x : ℝ) : (coeff w).1*x+(coeff w).2=w.val x := by
  cases w <;> dsimp [coeff,Wall.val] <;> ring

def width (v : Tag×Tag) (k : ℤ) : MiddleCapExpr :=
  .line ((k:ℝ)*((coeff v.2.val).1-(coeff v.1.val).1))
        ((k:ℝ)*((coeff v.2.val).2-(coeff v.1.val).2))

theorem width_eval (t : Scale) (v : Tag×Tag) (k : ℤ) :
    (((loc t v.2-loc t v.1)*k:ℤ):ℝ)=4*(t.d:ℝ)*(width v k).eval t.ratio := by
  push_cast
  simp only [loc,Wall.scaled,←coeff_val,width,MiddleCapExpr.eval]
  ring

def sumExpr {α : Type} (xs : List α) (f : α → MiddleCapExpr) :=
  xs.foldr (fun v tail=>.add (f v) tail) (.line 0 0 : MiddleCapExpr)

theorem sum_eval {α : Type} (xs : List α) (f : α → MiddleCapExpr) (x : ℝ) :
    (sumExpr xs f).eval x = (xs.map (fun v=>(f v).eval x)).sum := by
  induction xs with
  | nil => simp [sumExpr,MiddleCapExpr.eval]
  | cons v vs ih => exact congrArg ((f v).eval x+·) ih

def slotPop (o : Option ℕ) (a : Array ℤ) (j : ℕ) : ℤ := match o with
  | none => ∑ r ∈ range a.size,eligible j a[r]!
  | some q => population a q j

def events (bs : Classes) : Option ℕ → List Event
  | none => bs.flatMap allAt
  | some q => folded bs q

def layerExpr (s : Scale) (o : Option ℕ) (j : ℕ) : MiddleCapExpr :=
  .minimum (.line 0 40) (sumExpr (tiles s) (fun v=>width v (slotPop o (bag s v).toArray j)))

theorem valid_classes (t : Scale) : ∀ B∈middleClasses (4*t.p) (4*t.d),
    0≤B.1 ∧ ∀ r<B.2.size,B.2[r]!≤16 := by
  have hp := t.hp
  have hd := t.hd
  simpa only [MiddleGrid.classes,Int.toNat_of_nonneg hp.le,Int.toNat_of_nonneg hd.le] using
    MiddleGrid.classes_valid t.d.toNat t.p.toNat (by omega)

theorem level_classes (t : Scale) (o : Option ℕ) (j : ℕ) (hj : 0<j) :
    let bs := middleClasses (4*t.p) (4*t.d)
    level (events bs o) j=(bs.map (fun b=>b.1*slotPop o b.2 j)).sum := by
  dsimp only
  cases o with
  | none => simp only [events,level_flatMap,allAt_level,slotPop]
  | some q => exact folded_population _ q j hj (fun b hb => (valid_classes t b hb).2)

theorem weighted_scale (t : Scale) (vs : List (Tag×Tag)) (k : Tag×Tag→ℤ) :
    (((vs.map (fun v=>(loc t v.2-loc t v.1)*k v)).sum:ℤ):ℝ) =
      (4*(t.d:ℝ))*(sumExpr vs (fun v=>width v (k v))).eval t.ratio := by
  rw [sum_eval]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons,List.sum_cons,Int.cast_add,mul_add,←ih,width_eval]

theorem cap_scale {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right)
    (o : Option ℕ) (j : ℕ) (hj : 0<j) :
    let bs := middleClasses (4*t.p) (4*t.d)
    ((min (40*(4*t.d)) (level (events bs o) j):ℤ):ℝ)=4*(t.d:ℝ)*(layerExpr s o j).eval t.ratio := by
  dsimp only
  rw [level_classes _ _ _ hj,classes_moving hr hs ht,List.map_map]
  change ((min _ (((tiles s).map (fun v=>(loc t v.2-loc t v.1)*slotPop o (bag s v).toArray j)).sum):ℤ):ℝ)=_
  rw [Int.cast_min,weighted_scale]
  have hd : (0:ℝ)≤4*(t.d:ℝ) := mul_nonneg (by norm_num) (by exact_mod_cast t.hd.le)
  simp only [layerExpr,MiddleCapExpr.eval,zero_mul,zero_add,mul_min_of_nonneg _ _ hd]
  push_cast
  congr 1 <;> ring

def layers (s : Scale) (o : Option ℕ) : ℕ → MiddleCapExpr
  | 0 => .line 0 0
  | k+1 => .add (layers s o k) (layerExpr s o (k+1))

theorem layers_scale {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right) (o : Option ℕ) :
    let bs := middleClasses (4*t.p) (4*t.d)
    ((cappedLayers (4*t.d) (book (events bs o) blank):ℤ):ℝ)=4*(t.d:ℝ)*(layers s o 16).eval t.ratio := by
  dsimp only
  rw [book_cap]
  have H (k : ℕ) :
      ((∑ j ∈ Ico 1 (k+1),min (40*(4*t.d)) (level (events (middleClasses (4*t.p) (4*t.d)) o) j):ℤ):ℝ)=
      4*(t.d:ℝ)*(layers s o k).eval t.ratio := by
    induction k with
    | zero => simp [layers,MiddleCapExpr.eval]
    | succ k ih =>
      rw [sum_Ico_succ_top (by omega : 1≤k+1),Int.cast_add,ih,cap_scale hr hs ht o (k+1) (by omega)]
      simp [layers,MiddleCapExpr.eval,mul_add]
  exact H _

def rowK (t : Scale) := ((80*(4*t.d))/(4*t.p)).toNat
def chargeExpr (K q : ℕ) : MiddleCapExpr :=
  .line (-(((K+q+1)*(K-q)/2:ℕ):ℝ)) (80*((K-q:ℕ):ℝ))

theorem charge_scale (t : Scale) (K q : ℕ) :
    ((rowCharge (4*t.p) (4*t.d) K q:ℤ):ℝ)=4*(t.d:ℝ)*(chargeExpr K q).eval t.ratio := by
  have hd : (t.d:ℝ)≠0 := by exact_mod_cast t.hd.ne'
  simp only [rowCharge,chargeExpr,MiddleCapExpr.eval,Scale.ratio]
  generalize ((K+q+1)*(K-q)/2:ℕ) = u
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  field_simp
  <;> ring

def scoreExpr (s : Scale) (K q : ℕ) : MiddleCapExpr := .add (chargeExpr K q) (layers s (some q) 16)
def rowExpr (s : Scale) : MiddleCapExpr :=
  (List.range (rowK s+1)).foldl (fun e q=>.minimum e (scoreExpr s (rowK s) q)) (layers s none 16)

theorem raw_row_eval {r : ArithRow} (hr : r∈middleRows) {s t : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (ht : t.ratio∈Ioo (r.left:ℝ) r.right) :
    let K := rowK t
    ((best (middleClasses (4*t.p) (4*t.d)) (4*t.p) (4*t.d) K (K+1):ℤ):ℝ) =
      4*(t.d:ℝ)*(rowExpr s).eval t.ratio := by
  have hK : rowK s=rowK t := congrArg Int.toNat (norm_floor hr hs ht 80 (by decide))
  let bs := middleClasses (4*t.p) (4*t.d)
  have hd : (0:ℝ)≤4*(t.d:ℝ) := mul_nonneg (by norm_num) (by exact_mod_cast t.hd.le)
  have sc (q : ℕ) : ((score bs (4*t.p) (4*t.d) (rowK t) q:ℤ):ℝ)=4*(t.d:ℝ)*(scoreExpr s (rowK t) q).eval t.ratio := by
    rw [score,Int.cast_add,charge_scale]
    have H := layers_scale hr hs ht (some q)
    change _+((cappedLayers _ (book (events _ (some q)) _):ℤ):ℝ)=_
    rw [H]
    simp [scoreExpr,MiddleCapExpr.eval,mul_add]
  have fold (xs : List ℕ) (a : ℤ) (e : MiddleCapExpr) (he : (a:ℝ)=4*(t.d:ℝ)*e.eval t.ratio) :
      ((xs.foldl (fun z q=>min z (score bs (4*t.p) (4*t.d) (rowK t) q)) a:ℤ):ℝ) =
      4*(t.d:ℝ)*(xs.foldl (fun z q=>MiddleCapExpr.minimum z (scoreExpr s (rowK t) q)) e).eval t.ratio := by
    induction xs generalizing a e with
    | nil => exact he
    | cons q qs ih =>
      apply ih
      rw [Int.cast_min,he,sc]
      exact (mul_min_of_nonneg _ _ hd).symm
  simp only [best,rowExpr,hK]
  exact fold _ _ _ (layers_scale hr hs ht none)

end OddZetaSix.B40a.Cert.Transport
