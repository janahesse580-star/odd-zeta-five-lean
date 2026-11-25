import OddZetaSix.B40a.Arithmetic.MiddleRealBag

namespace OddZetaSix.B40a
open Finset
noncomputable section

def middleSlotClass (n p : ℕ) (hp : 0<p) (c : Fin (p/2+1)) :=
  univ.filter (fun u : Fin (slotCount n) => OddZetaSix.foldMod p hp (slotCenter n u)=c)

/-- Even on a wall, there are at most two address lifts per period and
twelve true columns per site. The bound permits coincident folded walls. -/
theorem middleSlotClass_card (n p : ℕ) (hp : 0<p) (c : Fin (p/2+1)) :
    (middleSlotClass n p hp c).card ≤ 24*(25*n/p+1) := by
  let coord := fun u : Fin (slotCount n) => (slotEquiv n).symm u
  let t := fun u => (coord u).1.val
  have ht (u) : t u≤25*n := by have := (coord u).1.isLt; dsimp [t]; omega
  let enc := fun u => ((⟨t u/p,Nat.lt_succ_of_le (Nat.div_le_div_right (ht u))⟩ : Fin (25*n/p+1)),
    (decide (t u%p=c.val)), (coord u).2)
  have residual (u) (hu : u ∈ middleSlotClass n p hp c) :
      t u%p=c.val ∨ t u%p=p-c.val := by
    have hf := congrArg (fun v : Fin (p/2+1) => (v.val:ℤ)) (mem_filter.mp hu).2
    change ((OddZetaSix.foldMod p hp (-(t u:ℤ))).val:ℤ)=(c.val:ℤ) at hf
    rw [foldMod_val_eq_middleFoldWall,middleFoldWall_neg _ _ (by exact_mod_cast hp)] at hf
    unfold middleFoldWall at hf
    have hr : ((t u%p:ℕ):ℤ)=(t u:ℤ)%p := by simp
    rw [←hr] at hf
    have := Nat.mod_lt (t u) hp
    omega
  have H := Finset.card_le_card_of_injOn (s:=middleSlotClass n p hp c) (t:=univ) enc
    (fun _ _ => mem_univ _) (by
      intro u hu v hv h
      have hq := congrArg (fun z : Fin (25*n/p+1) × Bool × Fin 12 => z.1.val) h
      have hs := congrArg (fun z : Fin (25*n/p+1) × Bool × Fin 12 => z.2.1) h
      have ha := congrArg (fun z : Fin (25*n/p+1) × Bool × Fin 12 => z.2.2) h
      change t u/p=t v/p at hq
      change decide (t u%p=c.val)=decide (t v%p=c.val) at hs
      have hr : t u%p=t v%p := by
        have h1 := residual u hu
        have h2 := residual v hv
        by_cases huc : t u%p=c.val <;> by_cases hvc : t v%p=c.val <;> simp [huc,hvc] at hs <;> omega
      have he : t u=t v := by
        calc
          _ = t u%p+p*(t u/p) := (Nat.mod_add_div _ _).symm
          _ = t v%p+p*(t v/p) := by rw [hq,hr]
          _ = _ := Nat.mod_add_div _ _
      apply (slotEquiv n).symm.injective
      exact Prod.ext (Fin.ext he) ha)
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    show 2*12=24 by decide,Nat.mul_comm (25*n/p+1)] using H

/-- Uniform error per exceptional folded class on the entire certified
middle band. Constants are unnormalized, before PNT summation. -/
theorem middle_boundary_class_cost (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hsq : 84*n<p^2)
    (hband : 11*n≤20*p) (c : Fin (p/2+1)) :
    ∑ u ∈ middleSlotClass n p (Fact.out : p.Prime).pos c,slotCost n p u ≤ 17664 := by
  have hp := (Fact.out : p.Prime).pos
  have hq : 25*n/p<46 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hcnt := middleSlotClass_card n p hp c
  calc
    _ ≤ ∑ _u ∈ middleSlotClass n p hp c,16 := sum_le_sum (fun u _ => slotCost_le_16 _ _ hn hsq u)
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; change (middleSlotClass n p hp c).card * 16 ≤ 17664; omega

end
end OddZetaSix.B40a
