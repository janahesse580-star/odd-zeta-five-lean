import OddZetaSix.B40a.Arithmetic.MiddleStripGrid
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OddZetaSix.B40a.Cert.StripGrid
open Finset

private theorem one_le_list_sum {α : Type} (xs : List α) (g : α→ℤ)
    (hp : ∀ v∈xs,0≤g v) {v : α} (hv : v∈xs) : g v≤(xs.map g).sum := by
  induction xs with
  | nil => simp at hv
  | cons a xs ih =>
    have hh := hp a List.mem_cons_self
    have ht (x) (h : x∈xs) := hp x (List.mem_cons_of_mem _ h)
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hv with rfl|hv
    · have hsum : 0≤(xs.map g).sum := List.sum_nonneg (fun z h=>by
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h; exact ht _ hw)
      omega
    · have := ih ht hv; omega

private theorem list_sum_swap {α β : Type} [Fintype α] (xs : List β) (f : α→β→ℤ) :
    (∑ x : α,(xs.map (f x)).sum)=(xs.map (fun v=>∑ x : α,f x v)).sum := by
  induction xs with
  | nil => simp
  | cons v xs ih => simp only [List.map_cons,List.sum_cons,sum_add_distrib,ih]

/-- A global upper quadrature. Only the costs on the actual wall addresses
are charged separately. There is no charge for the number of open strips. -/
theorem upper_grid_sum (p : ℕ) (d : ℤ) (hp : 0<p)
    (S : ℤ×ℤ→Finset (Fin (p/2+1))) (W : Finset (Fin (p/2+1)))
    (f : Fin (p/2+1)→ℤ) (g : ℤ×ℤ→ℤ)
    (hg : ∀ v∈strips (4*p) (4*d),0≤g v)
    (hS : ∀ v∈strips (4*p) (4*d),S v=univ.filter (fun c=>v.1<4*(c.val:ℤ) ∧ 4*(c.val:ℤ)<v.2))
    (hc : ∀ c∉W,∃ v∈strips (4*p) (4*d),c∈S v ∧ f c≤g v) :
    4*∑ c,f c ≤ 4*(∑ c ∈ W,f c)+
      (((strips (4*p) (4*d)).map (fun v=>(v.2-v.1)*g v)).sum) := by
  classical
  let vs := strips (4*p) (4*d)
  let F := fun c v => if c∈S v then g v else 0
  have hF (c) (v) (h : v∈vs) : 0≤F c v := by dsimp [F]; split <;> simp_all [vs]
  have pt (c) : f c≤(if c∈W then f c else 0)+(vs.map (F c)).sum := by
    by_cases h : c∈W
    · rw [ite_eq_left h]; apply le_add_of_nonneg_right
      apply List.sum_nonneg; intro z hz
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz; exact hF c _ hv
    · obtain ⟨v,hv,hcv,hf⟩ := hc c h
      have hh := one_le_list_sum vs (F c) (hF c) hv
      simpa [F,h,hcv] using (show f c≤(vs.map (F c)).sum from
        hf.trans (by simpa only [F,ite_eq_left hcv] using hh))
  have H := sum_le_sum (s:=univ) (fun c _=>pt c)
  rw [sum_add_distrib,←sum_filter,filter_mem_eq_inter,univ_inter,list_sum_swap] at H
  have eq (v) : (∑ c,F c v)=(S v).card*g v := by
    simp [F,←sum_filter]
  simp_rw [eq] at H
  have width (v : ℤ×ℤ) (hv : v∈vs) : 4*((S v).card:ℤ)≤v.2-v.1 := by
    obtain ⟨a,b⟩ := v
    rw [hS _ hv]
    exact four_times_class_card_le_width _ _ _ _ hp hv
  have sumWidth (l : List (ℤ×ℤ)) (hl : ∀ v∈l,v∈vs) :
      4*(l.map (fun v=>(S v).card*g v)).sum≤(l.map (fun v=>(v.2-v.1)*g v)).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,←mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_right (width _ (hl _ List.mem_cons_self)) (hg _ (hl _ List.mem_cons_self)))
        (ih (fun v hv=>hl _ (List.mem_cons_of_mem _ hv)))
  have H' := sumWidth vs (fun _ h=>h)
  change _ ≤ _+(vs.map _).sum
  omega

end OddZetaSix.B40a.Cert.StripGrid
