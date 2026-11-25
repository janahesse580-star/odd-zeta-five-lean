import OddZetaSix.B40a.Arithmetic.ResidueCounts
import OddZetaSix.B40a.Arithmetic.HighBand

/-! The pole and zero residue populations of the actual twelve-block kernel. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

private theorem range_alias_eq (p len : ℕ) (x c : ℤ) (_hlen : len>0) :
    ((range len).filter (fun j : ℕ => (p : ℤ) ∣ (x+j)-c)).card =
      residueCount p x (x+(len : ℤ)-1) c := by
  unfold residueCount
  apply Finset.card_bij (fun (j : ℕ) _ => x+(j : ℤ))
  · intro j hj
    have hh := mem_filter.mp hj
    have h := mem_range.mp hh.1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hh.2⟩
  · intro j _ k _ hj
    omega
  · intro k hk
    have h := mem_filter.mp hk
    have hh := mem_Icc.mp h.1
    let j := (k-x).toNat
    have he : (j : ℤ) = k-x := Int.toNat_of_nonneg (by omega)
    refine ⟨j,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,by omega⟩
    rw [he,show x+(k-x)-c = k-c by ring]
    exact h.2

/-- All denominator factors at one centered congruence class, counted with
multiplicity across the actual pole blocks. -/
def kernelPoleAliasCount (n p : ℕ) (c : ℤ) : ℕ :=
  ∑ b : Fin 12, ((range (blockLen n b+1)).filter (fun j : ℕ =>
    (p : ℤ) ∣ (blockStart n b : ℤ)-(center n : ℤ)+(j : ℤ)-c)).card

/-- All rising factors in the numerator, with their fifth-power multiplicity.
The single central factor is kept out of the count. -/
def kernelZeroAliasCount (n p : ℕ) (c : ℤ) : ℕ :=
  5*(((range (25*n)).filter (fun j : ℕ => (p : ℤ) ∣
    (1 : ℤ)+(j : ℤ)-(center n : ℤ)-c)).card +
    ((range (25*n)).filter (fun j : ℕ => (p : ℤ) ∣
      93*(n : ℤ)+2+(j : ℤ)-(center n : ℤ)-c)).card)

theorem kernelPoleAliasCount_eq (n p : ℕ) (c : ℤ) :
    kernelPoleAliasCount n p c =
      6*residueCount p (-25*n) (25*n) c +
      4*residueCount p (-17*n) (17*n) c +
      2*residueCount p (-16*n) (16*n) c := by
  unfold kernelPoleAliasCount
  simp_rw [range_alias_eq p _ _ _ (Nat.succ_pos _)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,blockStart,blockLen,offsets,center,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  -- Normalize the three interval endpoints before collecting the repeated summands.
  norm_num
  ring_nf

theorem kernelZeroAliasCount_eq (n p : ℕ) (hn : 0<n) (c : ℤ) :
    kernelZeroAliasCount n p c =
      5*(residueCount p (-59*n) (-34*n-1) c+residueCount p (34*n+1) (59*n) c) := by
  unfold kernelZeroAliasCount center
  push_cast
  have h1 (j : ℕ) : (1 : ℤ)+j-(59*n+1)-c = -59*n+j-c := by ring
  have h2 (j : ℕ) : 93*(n : ℤ)+2+j-(59*n+1)-c = (34*n+1)+j-c := by ring
  simp_rw [h1,h2]
  rw [range_alias_eq p _ _ _ (by omega),range_alias_eq p _ _ _ (by omega)]
  push_cast
  congr 2 <;> ring

theorem normalization_val_first_layer (n p : ℕ) [Fact p.Prime]
    (hp2 : 2 < p) (hsq : 84*n < p^2) :
    padicValRat p (normalization n) =
      (6*(50*n/p : ℕ) : ℤ) + (4*(34*n/p : ℕ) : ℤ) + (2*(32*n/p : ℕ) : ℤ) -
        (10*(25*n/p : ℕ) : ℤ) := by
  have hv2 : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by decide) hp2)]
    rfl
  have hf (m : ℕ) : (((m.factorial : ℕ) : ℚ)) ≠ 0 := by positivity
  unfold normalization
  rw [padicValRat.div (mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr (fun _ _ => hf _)))
    (pow_ne_zero _ (hf _)),
    padicValRat.mul (by norm_num) (Finset.prod_ne_zero_iff.mpr (fun _ _ => hf _)),hv2,zero_add,
    padicValRat.pow,valProd]
  · have hd (b : Fin 12) : (50-2*offsets b)*n < p^2 :=
      ((Nat.mul_le_mul_right n (Nat.sub_le _ _)).trans (by omega : 50*n ≤ 84*n)).trans_lt hsq
    have hD (b : Fin 12) :
        padicValRat p ((((50-2*offsets b)*n).factorial : ℕ) : ℚ) =
          ((((50-2*offsets b)*n)/p : ℕ) : ℤ) :=
      padicValRat_factorial_lt_sq p _ (hd b)
    simp_rw [hD]
    rw [padicValRat_factorial_lt_sq _ _ (by omega : 25*n < p^2)]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,offsets,Matrix.cons_val_zero,Matrix.cons_val_succ,
      zero_add,add_zero]
    norm_num
    ring
  · exact fun _ _ => hf _

theorem finitePeriodicRaw_eq_kernel_counts (n p : ℕ) [Fact p.Prime] (hn : 0<n)
    (hp2 : 2 < p) (hsq : 84*n < p^2) (c : ℤ) :
    finitePeriodicRaw n p c =
      4 + (kernelPoleAliasCount n p c : ℤ) - (kernelZeroAliasCount n p c : ℤ) -
        padicValRat p (normalization n) := by
  rw [kernelPoleAliasCount_eq,kernelZeroAliasCount_eq n p hn,normalization_val_first_layer n p hp2 hsq]
  unfold finitePeriodicRaw
  push_cast
  ring

end OddZetaSix.B40a
