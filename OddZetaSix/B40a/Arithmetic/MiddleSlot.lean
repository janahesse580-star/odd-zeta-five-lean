import OddZetaSix.B40a.Arithmetic.MiddleAtom

namespace OddZetaSix.B40a
open Finset
noncomputable section

theorem middle_harmonic_indicator (n p t l : ℕ) (ht : t≤25*n) :
    harmonicIndicator n p (center n+t) l =
      if Even l then (if 0<(34*n+t)/p then 1 else 0)
      else (if (34*n-t)/p < (34*n+t)/p then 1 else 0) := by
  unfold harmonicIndicator
  have h1 : center n+t-25*n-1=34*n+t := by unfold center; omega
  have h2 : kernelReflectedPole n (center n+t)-25*n-1=34*n-t := by
    unfold kernelReflectedPole center; omega
  rw [h1,h2]
  rfl

/-- Explicit floor-model cost for an individual order in the open middle
classes. All inputs to this function are integers, including harmonic cutoffs. -/
def middleOrderTerm (n p t r l : ℕ) : ℕ :=
  let m := middleMultiplicity n t
  let z := middleZeroAliases n p t
  let d := middlePoleAliases n p t-(m:ℤ)
  let v := z-d+6*((50*n/p:ℕ):ℤ)+4*((34*n/p:ℕ):ℤ)+2*((32*n/p:ℕ):ℤ)-10*((25*n/p:ℕ):ℤ)
  let loss := m-1-l-r
  let penalty := if d=0 then min loss z.toNat else loss
  let h : ℕ := if Even l then (if 0<(34*n+t)/p then 1 else 0)
               else (if (34*n-t)/p < (34*n+t)/p then 1 else 0)
  ((r:ℤ)-v+(penalty:ℤ)+((l+5:ℕ):ℤ)*(h:ℤ)).toNat

def middleSlot (n p t a : ℕ) : ℕ :=
  let m := middleMultiplicity n t
  ((range m).filter (fun r => a≤r)).sup fun r =>
    ((range m).filter (fun l => r≤m-1-l)).sup fun l => middleOrderTerm n p t r l

theorem middle_refined_slot (n p t a : ℕ) [Fact p.Prime] (hn : 0<n)
    (hp : 2<p) (hsq : 84*n<p^2) (ht : t≤25*n) (h16 : t≠16*n) (h17 : t≠17*n)
    (hw : middleAway n p (t:ℤ)) :
    refinedSlotCost n p (center n+t) a = middleSlot n p t a := by
  have hr := middle_order_open _ _ ht h16 h17
  have hv := middle_site_valuation n p t hn hp hsq ht h16 h17 hw
  obtain ⟨ha,hz⟩ := middle_kernel_aliases n p hn (by omega) t hw
  have hd : kernelDenomAliases n p (center n+t) =
      middlePoleAliases n p t-(middleMultiplicity n t:ℤ) := by
    unfold kernelDenomAliases
    simp only [Nat.cast_add,add_sub_cancel_left,ha,hr]
  have hz' : numAliasCount n p (center n+t) = (middleZeroAliases n p t).toNat := by
    unfold numAliasCount
    simp only [Nat.cast_add,add_sub_cancel_left,←hz,Int.toNat_natCast]
  unfold refinedSlotCost middleSlot refinedOrderCost effectiveOrderLoss middleOrderTerm
  simp_rw [hr,hv,hd,hz',middle_harmonic_indicator n p t _ ht]

end
end OddZetaSix.B40a
