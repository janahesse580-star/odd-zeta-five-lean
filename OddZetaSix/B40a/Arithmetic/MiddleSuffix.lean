import OddZetaSix.B40a.Arithmetic.MiddleSlot
import OddZetaSix.B40a.Certificate.Arithmetic

namespace OddZetaSix.B40a
open Finset

/-- Abstract integer implementation of the descending Taylor-order accumulator
in the original certificate. -/
def siteUpdate (m : ℕ) (φ : ℕ → ℕ → ℤ) (s : ℤ × List ℤ) (a : ℕ) : ℤ × List ℤ :=
  let v := (Cert.nrange 1 (m-a+1)).foldl (fun b e => max b (φ a e)) s.1
  (v,if 0<v then v::s.2 else s.2)

def siteOrder (m : ℕ) (φ : ℕ → ℕ → ℤ) (a : ℕ) :=
  (Cert.nrange 1 (m-a+1)).toFinset.sup fun e => (φ a e).toNat
def suffixSlot (m : ℕ) (φ : ℕ → ℕ → ℤ) (a : ℕ) :=
  ((range m).filter (fun r => a≤r)).sup (siteOrder m φ)

private theorem fold_max_int (xs : List ℕ) (f : ℕ → ℤ) (b : ℕ) :
    xs.foldl (fun k e => max k (f e)) (b:ℤ) =
      ((max b (xs.toFinset.sup (fun e => (f e).toNat)) : ℕ):ℤ) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.toFinset_cons,Finset.sup_insert]
    rw [show max (b:ℤ) (f x) = ((max b (f x).toNat:ℕ):ℤ) by omega, ih,max_assoc]

private theorem suffixSlot_step (m a : ℕ) (φ : ℕ → ℕ → ℤ) (ha : a<m) :
    suffixSlot m φ a = max (suffixSlot m φ (a+1)) (siteOrder m φ a) := by
  unfold suffixSlot
  have hset : (range m).filter (fun j => a≤j) =
      insert a ((range m).filter (fun j => a+1≤j)) := by
    ext x
    simp only [mem_filter,mem_insert,mem_range]
    omega
  rw [hset,sup_insert,max_comm]

private theorem suffix_states (φ : ℕ → ℕ → ℤ) (m a len : ℕ) (h : a+len=m) :
    (List.range' a len).reverse.foldl (siteUpdate m φ) (0,[]) =
      ((suffixSlot m φ a : ℤ),((List.range' a len).map (fun r => (suffixSlot m φ r:ℤ))).filter (fun z=>decide (0<z))) := by
  induction len generalizing a with
  | zero =>
    have ha : a=m := by omega
    subst a
    have he : (range m).filter (fun j => m≤j) = ∅ := by
      ext x; simp only [mem_filter,mem_range,Finset.notMem_empty,iff_false]; omega
    simp [suffixSlot,he]
  | succ len ih =>
    have ha : a<m := by omega
    rw [List.range'_succ]
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons]
    rw [ih (a+1) (by omega)]
    unfold siteUpdate
    have hv : max (suffixSlot m φ (a+1)) ((Cert.nrange 1 (m-a+1)).toFinset.sup (fun e => (φ a e).toNat)) =
        suffixSlot m φ a := (suffixSlot_step m a φ ha).symm
    simp only [fold_max_int,hv]
    by_cases hp : 0 < suffixSlot m φ a <;> simp [hp]

theorem site_suffix_values (m : ℕ) (φ : ℕ → ℕ → ℤ) :
    (((List.range m).reverse.foldl (siteUpdate m φ) (0,[])).2) =
      ((List.range m).map (fun r => (suffixSlot m φ r:ℤ))).filter (fun z=>decide (0<z)) := by
  have h := congrArg Prod.snd (suffix_states φ m 0 m (by omega))
  simpa only [List.range_eq_range'] using h

/-- The site formula as written in the midpoint evaluator. -/
def certificateAtom (p d t : ℤ) (a e : ℕ) : ℤ :=
  let count (l r : ℤ) := (r*d-t)/p-(l*d-t)/p
  let m : ℕ := 6+(if t<17*d then 4 else 0)+(if t<16*d then 2 else 0)
  let nd := 6*count (-25) 25+4*count (-17) 17+2*count (-16) 16-(m:ℤ)
  let nz := 5*(count (-59) (-34)+count 34 59)
  let v := nz-nd+6*(50*d/p)+4*(34*d/p)+2*(32*d/p)-10*(25*d/p)
  let l := (34*d-t)/p
  let r := (34*d+t)/p
  let loss := m-e-a
  let inc := if 0<nd then (loss:ℤ) else min (loss:ℤ) nz
  let bad := if e%2=1 then 0<r else l≠r
  (a:ℤ)-v+inc+(if bad then (e:ℤ)+4 else 0)

theorem middleSite_eq_suffix (p d t : ℤ) :
    let m : ℕ := 6+(if t<17*d then 4 else 0)+(if t<16*d then 2 else 0)
    Cert.middleSite p d t =
      ((List.range m).map (fun r => (suffixSlot m (certificateAtom p d t) r:ℤ))).filter
        (fun z => decide (0<z)) := by
  exact site_suffix_values _ _

end OddZetaSix.B40a
