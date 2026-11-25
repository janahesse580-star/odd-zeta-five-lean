import OddZetaSix.B40a.Certificate.Arithmetic
import Mathlib.Tactic.Ring

namespace OddZetaSix.B40a.Cert
namespace Sweep

abbrev Classes := List (ℤ × Array ℤ)
abbrev Event := ℤ × ℤ

def blank : Array ℤ := Array.replicate 17 0
def post (h : Array ℤ) (e : Event) := bump h e.1 e.2
def book (es : List Event) (h : Array ℤ) := es.foldl post h

def allAt (b : ℤ × Array ℤ) : List Event :=
  b.2.toList.map fun w => (w,b.1)
def headAt (q : ℕ) (b : ℤ × Array ℤ) : List Event :=
  if q<b.2.size then [(b.2[q]!,b.1)] else []
def tailAt (q : ℕ) (b : ℤ × Array ℤ) : List Event :=
  (nrange (q+1) (min (q+8) b.2.size)).flatMap fun j =>
    let w := b.2[j]! - 2*((j-q:ℕ):ℤ)
    if 0<w then [(w,b.1)] else []
def heads (bs : Classes) (t : ℕ) : List Event :=
  (List.range t).flatMap fun q => bs.flatMap (headAt q)
def folded (bs : Classes) (q : ℕ) := heads bs (q+1) ++ bs.flatMap (tailAt q)

def rowCharge (p d : ℤ) (K q : ℕ) :=
  80*d*((K-q:ℕ):ℤ)-p*(((K+q+1)*(K-q)/2:ℕ):ℤ)

def step (bs : Classes) (p d : ℤ) (K : ℕ) (s : Array ℤ × ℤ) (q : ℕ) :=
  let prior := book (bs.flatMap (headAt q)) s.1
  let hist := book (bs.flatMap (tailAt q)) prior
  (prior,min s.2 (rowCharge p d K q + cappedLayers d hist))

def score (bs : Classes) (p d : ℤ) (K q : ℕ) :=
  rowCharge p d K q + cappedLayers d (book (folded bs q) blank)
def best (bs : Classes) (p d : ℤ) (K t : ℕ) :=
  (List.range t).foldl (fun v q => min v (score bs p d K q))
    (cappedLayers d (book (bs.flatMap allAt) blank))

private theorem book_append (e f : List Event) (h : Array ℤ) :
    book (e++f) h=book f (book e h) := List.foldl_append

theorem sweep_invariant (bs : Classes) (p d : ℤ) (K t : ℕ) :
    (List.range t).foldl (step bs p d K) (blank,cappedLayers d (book (bs.flatMap allAt) blank)) =
      (book (heads bs t) blank,best bs p d K t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ,List.foldl_append,ih]
    simp only [List.foldl_cons,List.foldl_nil,step,heads,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,book_append,best,List.foldl_append,
      score,folded]

private theorem allAt_book (bs : Classes) (h : Array ℤ) :
    book (bs.flatMap allAt) h =
      bs.foldl (fun h (qty,bag) => bag.foldl (fun s w => bump s w qty) h) h := by
  unfold book
  rw [List.foldl_flatMap]
  apply congrArg (fun f => bs.foldl f h)
  funext H b
  rcases b with ⟨qty,bag⟩
  simp only [allAt,List.foldl_map,Array.foldl_toList,post]

private theorem headAt_book (bs : Classes) (q : ℕ) (h : Array ℤ) :
    book (bs.flatMap (headAt q)) h =
      bs.foldl (fun h (qty,bag) => if q<bag.size then bump h bag[q]! qty else h) h := by
  unfold book
  rw [List.foldl_flatMap]
  apply congrArg (fun f => bs.foldl f h)
  funext h b
  rcases b with ⟨qty,bag⟩
  unfold headAt
  dsimp only
  split <;> rfl

private theorem tailAt_book (bs : Classes) (q : ℕ) (h : Array ℤ) :
    book (bs.flatMap (tailAt q)) h =
      bs.foldl (fun h (qty,bag) => (nrange (q+1) (min (q+8) bag.size)).foldl (fun acc j =>
        let w := bag[j]!-2*((j-q:ℕ):ℤ)
        if 0<w then bump acc w qty else acc) h) h := by
  unfold book
  rw [List.foldl_flatMap]
  apply congrArg (fun f => bs.foldl f h)
  funext h b
  rcases b with ⟨qty,bag⟩
  unfold tailAt
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (nrange (q+1) (min (q+8) bag.size)).foldl f h)
  funext s j
  dsimp only
  split <;> rfl

/-- The original executable's optimum is the minimum of the unfolded
choice and all folded choices, with the true prefix and penalized suffix. -/
theorem middleValue_eq_best (x : ℚ) :
    let p := 4*x.num
    let d := 4*(x.den:ℤ)
    let K := (80*d/p).toNat
    middleValue x = (best (middleClasses p d) p d K (K+1):ℚ)/(2000*d:ℤ) := by
  dsimp only
  let p := 4*x.num
  let d := 4*(x.den:ℤ)
  let bs := middleClasses p d
  let K := (80*d/p).toNat
  have H := congrArg (fun pair : Array ℤ × ℤ => (pair.2:ℚ)/(2000*d:ℤ))
    (sweep_invariant bs p d K (K+1))
  have heq : step bs p d K = fun (s : Array ℤ × ℤ) (q : ℕ) =>
      let prior := bs.foldl (fun h (qty,bag) => if q<bag.size then bump h bag[q]! qty else h) s.1
      let hist := bs.foldl (fun h (qty,bag) =>
        (nrange (q+1) (min (q+8) bag.size)).foldl (fun h j =>
          let w := bag[j]!-2*((j-q:ℕ):ℤ)
          if 0<w then bump h w qty else h) h) prior
      (prior,min s.2 (rowCharge p d K q + cappedLayers d hist)) := by
    funext s q
    simp only [step,tailAt_book,headAt_book]
  rw [heq,allAt_book] at H
  exact H

end Sweep
end OddZetaSix.B40a.Cert
