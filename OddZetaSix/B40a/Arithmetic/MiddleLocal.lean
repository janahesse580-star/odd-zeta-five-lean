import OddZetaSix.B40a.Arithmetic.KernelResidues

/-! Exact denominator-alias valuations in the single-layer regime, adapted from
the original MIT-licensed SixLocalSlots argument. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

def kernelDenomAliases (n p k : ℕ) : ℤ :=
  (kernelPoleAliasCount n p ((k : ℤ)-(center n : ℤ)) : ℤ) - (kernelPoleOrder n k : ℤ)

theorem kernelCofactor_first_layer (n p : ℕ) [Fact p.Prime] (_hn : 0 < n)
    (hsq : 84 * n < p ^ 2) (k : ℕ) (hk : k ∈ kernelPoleSet n) :
    (kernelLocalCofactor n k).coeff 0 ≠ 0 ∧
    padicValRat p ((kernelLocalCofactor n k).coeff 0) = kernelDenomAliases n p k ∧
    PolyWeighted p (kernelLocalCofactor n k) (kernelDenomAliases n p k) 1 ∧
    PolyWeighted p (kernelLocalCofactor n k) 0 0 := by
  have hp : p.Prime := Fact.out
  have hbnd := kernel_pole_address_bounds n k hk
  let s_b : Fin 12 → Finset ℕ := fun b =>
    if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
      (range (blockLen n b + 1)).erase (k - blockStart n b)
    else range (blockLen n b + 1)
  have hrew : kernelLocalCofactor n k =
      ∏ b : Fin 12, ∏ j ∈ s_b b, (X + C (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) :=
    kernelLocalCofactor_eq_block_prod n k hk
  have hdist : ∀ (b : Fin 12), ∀ j ∈ s_b b,
      ((blockStart n b + j : ℤ) - (k : ℤ)) ≠ 0 ∧
      ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs < p ^ 2 := by
    intro b j hj
    have hob : offsets b ≤ 9 := by fin_cases b <;> decide
    have hSb : 34 * n + 1 ≤ blockStart n b ∧ blockStart n b + blockLen n b ≤ 84 * n + 1 := by
      unfold blockStart blockLen
      have h0 : (34 + offsets b) * n = 34 * n + offsets b * n := by ring
      have h1 : offsets b * n ≤ 9 * n := Nat.mul_le_mul_right n hob
      have h2 : (50 - 2 * offsets b) * n + 2 * (offsets b * n) = 50 * n := by
        have : (50 - 2 * offsets b) + 2 * offsets b = 50 := by omega
        calc
          (50 - 2 * offsets b) * n + 2 * (offsets b * n)
              = ((50 - 2 * offsets b) + 2 * offsets b) * n := by ring
          _ = 50 * n := by rw [this]
      omega
    dsimp [s_b] at hj
    split_ifs at hj with hcond
    · have hne := (Finset.mem_erase.mp hj).1
      have hlt := mem_range.mp (Finset.mem_erase.mp hj).2
      omega
    · have hlt := mem_range.mp hj
      omega
  have hval_lin : ∀ (b : Fin 12), ∀ j ∈ s_b b,
      padicValRat p ((((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
        if (p : ℤ) ∣ (blockStart n b + j : ℤ) - (k : ℤ) then 1 else 0 := by
    intro b j hj
    have hd := hdist b j hj
    rw [padicValRat.of_int, padicValInt]
    split_ifs with hdvd
    · have h1 : 1 ≤ padicValNat p ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs :=
        one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hd.1)
          (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd))
      have hlt2 : padicValNat p ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs < 2 := by
        by_contra hge
        push Not at hge
        have hp2dvd : p ^ 2 ∣ ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs :=
          (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd.1)).mpr hge
        have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd.1) hp2dvd
        omega
      omega
    · have hnd : ¬ p ∣ ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs := fun h =>
        hdvd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd
  have hsum_eq : (∑ b : Fin 12, ∑ j ∈ s_b b,
      (if (p : ℤ) ∣ (blockStart n b + j : ℤ) - (k : ℤ) then (1 : ℤ) else 0)) =
      kernelDenomAliases n p k := by
    unfold kernelDenomAliases kernelPoleAliasCount
    have hord_sum : (kernelPoleOrder n k : ℤ) = ∑ b : Fin 12,
        if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (1 : ℤ) else 0 := by
      have h := congrArg (Nat.cast (R := ℤ)) (kernelPoleOrder_eq_block_count n k).symm
      push_cast at h
      simpa [apply_ite] using h
    rw [hord_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _
    have hfull : (((range (blockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ (blockStart n b : ℤ) - (center n : ℤ)+(j : ℤ) - ((k : ℤ)-(center n : ℤ)))).card : ℤ) =
        ∑ j ∈ range (blockLen n b + 1),
          if (p : ℤ) ∣ (blockStart n b + j : ℤ) - (k : ℤ) then (1 : ℤ) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1; congr 1; ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; constructor <;> intro h <;> (convert h using 1; ring)
    rw [hfull]
    dsimp [s_b]
    split_ifs with hcond
    · have hmem : k - blockStart n b ∈ range (blockLen n b + 1) :=
        mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hmem]
      have h0 : (blockStart n b + ((k - blockStart n b : ℕ) : ℤ)) - (k : ℤ) = 0 := by
        rw [Nat.cast_sub hcond.1]; ring
      rw [h0]
      simp
    · ring
  have hcoeff0 : (kernelLocalCofactor n k).coeff 0 =
      ∏ b : Fin 12, ∏ j ∈ s_b b, (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) := by
    rw [hrew, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
    apply Finset.prod_congr rfl; intro b _
    rw [eval_prod]
    apply Finset.prod_congr rfl; intro j _; simp
  have hne0 : (kernelLocalCofactor n k).coeff 0 ≠ 0 := by
    rw [hcoeff0]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
      Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist b j hj).1))
  have hval0 : padicValRat p ((kernelLocalCofactor n k).coeff 0) = kernelDenomAliases n p k := by
    have hpadic_prod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℚ),
        (∀ i ∈ s, f i ≠ 0) → padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
      intro ι s f hf
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValRat.mul (hf a (mem_insert_self _ _))
            (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (mem_insert_of_mem hb))),
          ih (fun b hb => hf b (mem_insert_of_mem hb))]
    have houter := hpadic_prod (Finset.univ : Finset (Fin 12))
      (fun b => ∏ j ∈ s_b b, (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
      (fun b _ => Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist b j hj).1))
    rw [hcoeff0, houter, ← hsum_eq]
    apply Finset.sum_congr rfl; intro b _
    rw [hpadic_prod (s_b b) _ (fun j hj => by exact_mod_cast (hdist b j hj).1)]
    exact Finset.sum_congr rfl (fun j hj => hval_lin b j hj)
  have hwt1 : PolyWeighted p (kernelLocalCofactor n k) (kernelDenomAliases n p k) 1 := by
    rw [hrew, ← hsum_eq]
    exact polyWeighted_prod (p := p) Finset.univ _ _ 1 (fun b _ =>
      polyWeighted_prod (p := p) (s_b b) _ _ 1 (fun j _ => polyWeighted_linear_int _))
  have hwt0 : PolyWeighted p (kernelLocalCofactor n k) 0 0 := by
    rw [hrew]
    have houter := polyWeighted_prod (p := p) (Finset.univ : Finset (Fin 12))
      (fun b => ∏ j ∈ s_b b, (X + C (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)))
      (fun _ => (0 : ℤ)) 0 (fun b _ => by
        have hinner := polyWeighted_prod (p := p) (s_b b)
          (fun j => X + C (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
          (fun _ => (0 : ℤ)) 0
          (fun j _ => polyWeighted_linear_int_slope _ 0 le_rfl)
        rwa [Finset.sum_const_zero] at hinner)
    rwa [Finset.sum_const_zero] at houter
  exact ⟨hne0, hval0, hwt1, hwt0⟩


/-- Series division keeps the exact order loss used in the folded model.
A unit cofactor consumes at most the number of numerator aliases. -/
theorem localQuotient_first_layer {p : ℕ} [Fact p.Prime] {A D : ℚ[X]} {v nd : ℤ} {nz : ℕ}
    (hDv : padicValRat p (D.coeff 0) = nd)
    (hD0 : PolyWeighted p D 0 0) (hD1 : PolyWeighted p D nd 1)
    (hA : ∀ r : ℕ, ValAtLeast p (v+(nz : ℤ)-(min r nz : ℤ)) (A.coeff r)) :
    ∀ r : ℕ, ValAtLeast p
      (v+(nz : ℤ)-nd-(if nd=0 then min r nz else r : ℕ)) (localQuotient A D r) := by
  have hInv : ValAtLeast p (-nd) (D.coeff 0)⁻¹ := by
    right
    rw [padicValRat.inv,hDv]
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [localQuotient,div_eq_mul_inv]
    let d : ℕ → ℕ := fun j => if nd=0 then min j nz else j
    have hSub : ValAtLeast p (v+(nz : ℤ)-(d r : ℤ))
        (A.coeff r - ∑ j : Fin r, D.coeff (r-j.val) * localQuotient A D j.val) := by
      apply valAtLeast_sub
      · apply valAtLeast_mono (hA r)
        dsimp [d]
        split_ifs <;> omega
      · apply valAtLeast_sum
        intro j _
        have hJ := ih j.val j.isLt
        by_cases he : nd=0
        · have hb := valAtLeast_mul (hD0 (r-j.val)) hJ
          apply valAtLeast_mono hb
          dsimp [d]
          rw [ite_eq_left he,ite_eq_left he,he]
          have ht : min j.val nz ≤ min r nz := min_le_min_right _ j.isLt.le
          simp only [zero_mul,sub_zero]
          omega
        · have hb := valAtLeast_mul (hD1 (r-j.val)) hJ
          apply valAtLeast_mono hb
          dsimp [d]
          rw [ite_eq_right he,ite_eq_right he,Nat.cast_sub j.isLt.le]
          omega
    apply valAtLeast_mono (valAtLeast_mul hSub hInv)
    dsimp [d]
    omega

end OddZetaSix.B40a
