import OddZetaSix.B40a.Arithmetic.FoldedContent

/-! Exact floor counts for the open classes in the middle certificate. -/
namespace OddZetaSix.B40a
open Finset

def middleCount (n p : ℕ) (c a b : ℤ) : ℤ := (b*n-c)/p-(a*n-c)/p

def middleAway (n p : ℕ) (c : ℤ) :=
  ∀ e ∈ ([-25,-17,-16,-59,-34] : List ℤ), ¬ (p:ℤ) ∣ e*n-c

def middlePoleAliases (n p : ℕ) (c : ℤ) : ℤ :=
  6*middleCount n p c (-25) 25+4*middleCount n p c (-17) 17+
    2*middleCount n p c (-16) 16

def middleZeroAliases (n p : ℕ) (c : ℤ) : ℤ :=
  5*(middleCount n p c (-59) (-34)+middleCount n p c 34 59)

def middleMultiplicity (n t : ℕ) : ℕ :=
  6+(if t<17*n then 4 else 0)+(if t<16*n then 2 else 0)

theorem middle_kernel_aliases (n p : ℕ) (hn : 0<n) (hp : 0<p) (c : ℤ)
    (hw : middleAway n p c) :
    (kernelPoleAliasCount n p c : ℤ) = middlePoleAliases n p c ∧
    (kernelZeroAliasCount n p c : ℤ) = middleZeroAliases n p c := by
  have closed (a b : ℤ) (h : a≤b) (he : a ∈ ([-25,-17,-16,-59,-34]:List ℤ)) :
      (residueCount p (a*n) (b*n) c:ℤ) = middleCount n p c a b := by
    have H := residue_closed_normalized a b c n p hp h
    rw [periodicCount_rational _ _ _ _ _ hp,ite_eq_right (hw a he)] at H
    unfold middleCount; omega
  have left := residue_left_closed_normalized (-59) (-34) c n p hp hn (by decide)
  rw [periodicCount_rational _ _ _ _ _ hp] at left
  unfold endpointAlias at left
  rw [ite_eq_right (hw (-59) (by decide)),ite_eq_right (hw (-34) (by decide))] at left
  have right := residue_right_closed_normalized 34 59 c n p hp hn (by decide)
  rw [periodicCount_rational _ _ _ _ _ hp] at right
  constructor
  · rw [kernelPoleAliasCount_eq]; push_cast
    rw [closed (-25) 25 (by decide) (by decide),closed (-17) 17 (by decide) (by decide),
      closed (-16) 16 (by decide) (by decide)]
    rfl
  · rw [kernelZeroAliasCount_eq _ _ hn]; push_cast
    unfold middleZeroAliases middleCount
    omega

theorem middle_order_open (n t : ℕ) (ht : t≤25*n) (h16 : t≠16*n) (h17 : t≠17*n) :
    kernelPoleOrder n (center n+t) = middleMultiplicity n t := by
  rw [←kernelPoleOrder_eq_block_count]
  have hc (b : Fin 12) :
      (if blockStart n b ≤ center n+t ∧ center n+t ≤ blockStart n b+blockLen n b then 1 else 0 : ℕ) =
      (if b.val<6 then 1 else if b.val<10 then (if t<17*n then 1 else 0)
        else (if t<16*n then 1 else 0)) := by
    fin_cases b <;> simp [blockStart,blockLen,center,offsets] <;> (first | omega | split_ifs <;> omega)
  simp_rw [hc]
  unfold middleMultiplicity
  split_ifs <;> decide

/-- This is the integer `v` used at a site in `Cert.middleSite`. -/
theorem middle_site_valuation (n p t : ℕ) [Fact p.Prime] (hn : 0<n)
    (hp : 2<p) (hsq : 84*n<p^2) (ht : t≤25*n) (h16 : t≠16*n) (h17 : t≠17*n)
    (hw : middleAway n p (t:ℤ)) :
    siteBaseVal n p (center n+t) =
      middleZeroAliases n p t - (middlePoleAliases n p t-(middleMultiplicity n t:ℤ)) +
      6*((50*n/p:ℕ):ℤ)+4*((34*n/p:ℕ):ℤ)+2*((32*n/p:ℕ):ℤ)-10*((25*n/p:ℕ):ℤ) := by
  obtain ⟨ha,hz⟩ := middle_kernel_aliases n p hn (by omega) (t:ℤ) hw
  unfold siteBaseVal factVal numAliasCount kernelDenomAliases
  simp only [Nat.cast_add,add_sub_cancel_left]
  rw [ha,hz,middle_order_open _ _ ht h16 h17,normalization_val_first_layer _ _ hp hsq]
  ring

end OddZetaSix.B40a
