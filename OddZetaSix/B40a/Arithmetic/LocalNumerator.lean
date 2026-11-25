import OddZetaSix.B40a.Arithmetic.MiddleLocal

/-! Numerator alias valuations and the concrete Taylor quotient bound. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

private theorem val_int_single_layer (p : ℕ) [Fact p.Prime] (z : ℤ)
    (hz : z ≠ 0) (hZ : z.natAbs < p^2) :
    padicValRat p (z : ℚ) = if (p : ℤ) ∣ z then 1 else 0 := by
  rw [padicValRat.of_int,padicValInt]
  by_cases hd : p ∣ z.natAbs
  · have h1 := one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hz) hd
    have h2 : padicValNat p z.natAbs < 2 := by
      by_contra! h
      exact (not_le_of_gt hZ) (Nat.le_of_dvd (Int.natAbs_pos.mpr hz)
        ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)).mpr h))
    have hd' : (p : ℤ) ∣ z := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
    simp [hd']
    omega
  · have hd' : ¬ (p : ℤ) ∣ z := fun h => hd (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h))
    simp [hd',padicValNat.eq_zero_of_not_dvd hd]

private theorem rising_taylor_eq (a : ℤ) (m k : ℕ) :
    taylor (-(k : ℚ)) (rising (a : ℚ) m) =
      ∏ j ∈ range m, (X+C (((a+(j : ℤ)-(k : ℤ)) : ℤ) : ℚ)) := by
  unfold rising
  have h : taylor (-(k : ℚ)) (∏ j ∈ range m, (X+C ((a : ℚ)+(j : ℚ)))) =
      ∏ j ∈ range m, taylor (-(k : ℚ)) (X+C ((a : ℚ)+(j : ℚ))) :=
    map_prod (taylorAlgHom (-(k : ℚ))) _ _
  rw [h]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_add,taylor_X,taylor_C,add_assoc,← C_add]
  congr 2
  push_cast
  ring

private theorem rising_taylor_weight (p m k : ℕ) [Fact p.Prime] (a : ℤ)
    (h : ∀ j ∈ range m, a+(j : ℤ)-(k : ℤ) ≠ 0 ∧
      (a+(j : ℤ)-(k : ℤ)).natAbs < p^2) :
    PolyWeighted p (taylor (-(k : ℚ)) (rising (a : ℚ) m))
      (((range m).filter (fun j : ℕ => (p : ℤ) ∣ a+(j : ℤ)-(k : ℤ))).card : ℤ) 1 ∧
    PolyWeighted p (taylor (-(k : ℚ)) (rising (a : ℚ) m)) 0 0 := by
  rw [rising_taylor_eq]
  constructor
  · have hc : (((range m).filter (fun j : ℕ => (p : ℤ) ∣ a+(j : ℤ)-(k : ℤ))).card : ℤ) =
        ∑ j ∈ range m, padicValRat p (((a+(j : ℤ)-(k : ℤ)) : ℤ) : ℚ) := by
      rw [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      rw [val_int_single_layer p _ (h j hj).1 (h j hj).2]
      split_ifs <;> simp
    rw [hc]
    apply polyWeighted_prod _ _ _ 1
    intro j hj
    rw [val_int_single_layer p _ (h j hj).1 (h j hj).2]
    exact polyWeighted_linear_int _
  · simpa using polyWeighted_prod (p := p) (range m)
      (fun j => X+C (((a+(j : ℤ)-(k : ℤ)) : ℤ) : ℚ)) (fun _ => 0) 0
      (fun j _ => polyWeighted_linear_int_slope _ 0 le_rfl)

private theorem polyWeighted_pow_nat {p : ℕ} [Fact p.Prime] {P : ℚ[X]} {v s : ℤ}
    (h : PolyWeighted p P v s) (m : ℕ) : PolyWeighted p (P^m) ((m : ℤ)*v) s := by
  induction m with
  | zero => simpa using polyWeighted_one p s
  | succ m ih =>
    rw [pow_succ,Nat.cast_succ,add_mul,one_mul]
    exact polyWeighted_mul ih h

def baseKernelNumerator (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (C (normalization n) * numerator n)

theorem baseKernelNumerator_first_layer (n p k : ℕ) [Fact p.Prime]
    (hsq : 84*n < p^2) (hk : k ∈ kernelPoleSet n) :
    let nz := kernelZeroAliasCount n p ((k : ℤ)-(center n : ℤ))
    ∀ r : ℕ, ValAtLeast p (padicValRat p (normalization n)+(nz : ℤ)-((min r nz : ℕ) : ℤ))
      ((baseKernelNumerator n k).coeff r) := by
  let a := (1 : ℤ)
  let b := 93*(n : ℤ)+2
  let x := (center n : ℤ)-k
  let A := taylor (-(k : ℚ)) (rising (a : ℚ) (25*n))
  let B := taylor (-(k : ℚ)) (rising (b : ℚ) (25*n))
  let ka := ((range (25*n)).filter (fun j : ℕ => (p : ℤ) ∣ a+(j : ℤ)-(k : ℤ))).card
  let kb := ((range (25*n)).filter (fun j : ℕ => (p : ℤ) ∣ b+(j : ℤ)-(k : ℤ))).card
  have hk' := kernel_pole_address_bounds n k hk
  have hA := rising_taylor_weight p (25*n) k a (fun j hj => by
    have := mem_range.mp hj
    dsimp [a]
    omega)
  have hB := rising_taylor_weight p (25*n) k b (fun j hj => by
    have := mem_range.mp hj
    dsimp [b]
    omega)
  have hrew : baseKernelNumerator n k =
      C (normalization n)*(X+C (x : ℚ))*(A*B)^5 := by
    unfold baseKernelNumerator numerator
    have hx : taylor (-(k : ℚ)) (X+C (center n : ℚ)) = X+C (x : ℚ) := by
      rw [map_add,taylor_X,taylor_C,add_assoc,← C_add]
      congr 2
      dsimp [x]
      push_cast
      ring
    rw [taylor_mul,taylor_C,taylor_mul,hx,taylor_pow,taylor_mul]
    dsimp [A,B,a,b]
    push_cast
    ring
  have hcount : kernelZeroAliasCount n p ((k : ℤ)-(center n : ℤ)) = 5*(ka+kb) := by
    unfold kernelZeroAliasCount ka kb a b
    simp only [show ∀ j : ℕ, (1 : ℤ)+j-center n-((k : ℤ)-center n) = 1+j-k by intro j; ring,
      show ∀ j : ℕ, 93*(n : ℤ)+2+j-center n-((k : ℤ)-center n) = 93*(n : ℤ)+2+j-k by intro j; ring]
  let v := padicValRat p (normalization n)
  have hc : ValAtLeast p v (normalization n) := Or.inr le_rfl
  have hw1 : PolyWeighted p (baseKernelNumerator n k) (v + 5*((ka : ℤ)+(kb : ℤ))) 1 := by
    rw [hrew]
    have hab : PolyWeighted p (A*B) ((ka : ℤ)+(kb : ℤ)) 1 := polyWeighted_mul hA.1 hB.1
    simpa using polyWeighted_mul
      (polyWeighted_mul (polyWeighted_C hc) (polyWeighted_linear_int_slope x 1 (by decide)))
      (polyWeighted_pow_nat hab 5)
  have hw0 : PolyWeighted p (baseKernelNumerator n k) v 0 := by
    rw [hrew]
    have hab : PolyWeighted p (A*B) 0 0 := by simpa using polyWeighted_mul hA.2 hB.2
    simpa using polyWeighted_mul
      (polyWeighted_mul (polyWeighted_C hc) (polyWeighted_linear_int_slope x 0 le_rfl))
      (polyWeighted_pow_nat hab 5)
  dsimp only
  rw [hcount]
  intro r
  by_cases hh : r ≤ 5*(ka+kb)
  · rw [min_eq_left hh]
    apply valAtLeast_mono (hw1 r)
    push_cast
    omega
  · rw [min_eq_right (by omega)]
    apply valAtLeast_mono (hw0 r)
    omega

theorem kernelTaylorQuotient_first_layer (n p k : ℕ) [Fact p.Prime] (hn : 0<n)
    (hp : 84*n < p^2) (hk : k ∈ kernelPoleSet n) :
    let nz := kernelZeroAliasCount n p ((k : ℤ)-(center n : ℤ))
    let nd := kernelDenomAliases n p k
    ∀ d, ValAtLeast p (padicValRat p (normalization n)+(nz : ℤ)-nd-
        (if nd=0 then min d nz else d : ℕ))
      (localQuotient (baseKernelNumerator n k) (kernelLocalCofactor n k) d) := by
  obtain ⟨_,hd,hD1,hD0⟩ := kernelCofactor_first_layer n p hn hp k hk
  apply localQuotient_first_layer hd hD0 hD1
  intro r
  simpa only [Nat.cast_min] using baseKernelNumerator_first_layer n p k hp hk r

end OddZetaSix.B40a
