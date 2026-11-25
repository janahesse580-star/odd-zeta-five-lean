import OddZetaSix.B40a.Arithmetic.Valuation
import OddZetaSix.B40a.Identity.Evaluation

/-! Universal all-prime-power bound for the B40a kernel. The block argument is adapted from the MIT-licensed upstream SixSmallPrimes module. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators
/-- Block length `L_b = (50 - 2 * d_b) * n`. -/
def blockLen (n : ℕ) (b : Fin 12) : ℕ := (50 - 2 * offsets b) * n

/-- Block start `a_b = (34 + d_b) * n + 1`. -/
def blockStart (n : ℕ) (b : Fin 12) : ℕ := (34 + offsets b) * n + 1

/-- Normalized numerator `Ñ_k = (2 / ∏ (z_a n)!^2) * taylor (-k) (numerator * kernelCenteredMultiplier)`. -/
def normLocalNum (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ) : ℚ[X] :=
  C (2 / ((25*n).factorial : ℚ)^10) *
    taylor (-(k : ℚ)) (numerator n * kernelCenteredMultiplier n i.val j.val)

/-- Normalized cofactor `C̃_k = (1 / ∏ L_b!) * kernelLocalCofactor n k`. -/
def normLocalCof (n k : ℕ) : ℚ[X] :=
  C (1 / (∏ b : Fin 12, ((blockLen n b).factorial : ℚ))) * kernelLocalCofactor n k

theorem sixNormLocal_congruence (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ)
    (hk : k ∈ kernelPoleSet n) :
    X ^ kernelPoleOrder n k ∣
      normLocalNum n i j k - kernelLocalPrincipal n i j k * normLocalCof n k := by
  have hden_ne : (∏ b : Fin 12, ((blockLen n b).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => by exact_mod_cast Nat.factorial_ne_zero _)
  have hcong := kernelLocalPrincipal_congruence n i j k hk
  have hmul := dvd_mul_of_dvd_right hcong
    (C (1 / (∏ b : Fin 12, ((blockLen n b).factorial : ℚ))))
  have heq : C (1 / (∏ b : Fin 12, ((blockLen n b).factorial : ℚ))) *
      (kernelLocalNumerator n i j k - kernelLocalPrincipal n i j k * kernelLocalCofactor n k) =
      normLocalNum n i j k - kernelLocalPrincipal n i j k * normLocalCof n k := by
    unfold kernelLocalNumerator normLocalNum normLocalCof blockLen
    simp only [kernelNormalization,kernelNumerator,taylor_mul,taylor_C,mul_sub]
    rw [← mul_assoc, ← mul_assoc, ← map_mul]
    unfold normalization
    have hsc : (1 / (∏ b : Fin 12, (((50 - 2 * offsets b) * n).factorial : ℚ))) *
        ((2 * ∏ b : Fin 12, (((50 - 2 * offsets b) * n).factorial : ℚ)) /
          ((25*n).factorial : ℚ)^10) =
        2 / ((25*n).factorial : ℚ)^10 := by
      field_simp
    rw [hsc]
    ring
  rwa [heq] at hmul

private theorem taylor_prod_fin {ι : Type*} [DecidableEq ι] (x : ℚ)
    (s : Finset ι) (f : ι → ℚ[X]) :
    taylor x (∏ i ∈ s, f i) = ∏ i ∈ s, taylor x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [← C_1, taylor_C, C_1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, taylor_mul, ih]

/-- The normalized numerator loses at most the common logarithmic valuation per Taylor order. -/
theorem normLocalNum_weighted (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (i j : Fin (fiveRank n)) (k : ℕ) :
    PolyWeighted p (normLocalNum n i j k) 0 (Nat.log p (84 * n)) := by
  let S : ℤ := (Nat.log p (84*n) : ℤ)
  have hS : 0 ≤ S := Int.natCast_nonneg _
  let x : ℤ := (center n : ℤ)-k
  have hx : (x : ℚ) = 59*(n : ℚ)+1-k := by unfold x center; push_cast; ring
  have hcenter : taylor (-(k : ℚ)) (X + C (center n : ℚ)) = X + C (x : ℚ) := by
    rw [map_add,taylor_X,taylor_C,add_assoc,← C_add]
    congr 2
    unfold x
    push_cast
    ring
  have hmult : taylor (-(k : ℚ)) (kernelCenteredMultiplier n i.val j.val) =
      taylor (x : ℚ) (evenBasis i.val) * taylor (x : ℚ) (evenBasis j.val) := by
    rw [kernelCenteredMultiplier]
    simp only [taylor_apply,comp_assoc,add_comp,X_comp,C_comp,mul_comp]
    congr 1 <;> congr 1 <;> rw [add_assoc,← C_add,hx] <;> congr 2 <;> ring
  let A := taylor (-(k : ℚ)) (normalizedRising 1 (25*n))
  let B := taylor (-(k : ℚ)) (normalizedRising (93*(n : ℤ)+2) (25*n))
  have hab : A*B = C ((1 / ((25*n).factorial : ℚ))^2) *
      (taylor (-(k : ℚ)) (rising 1 (25*n)) *
        taylor (-(k : ℚ)) (rising (93*(n : ℚ)+2) (25*n))) := by
    simp only [A,B,normalizedRising,taylor_mul,taylor_C,map_pow]
    push_cast
    ring
  have hrew : normLocalNum n i j k =
      C (2 : ℚ)*(X+C (x : ℚ))*(A*B)^5*
        (taylor (x : ℚ) (evenBasis i.val) * taylor (x : ℚ) (evenBasis j.val)) := by
    unfold normLocalNum numerator
    rw [taylor_mul,hmult,taylor_mul,hcenter,taylor_pow,taylor_mul,hab]
    simp only [mul_pow, ← map_pow C]
    have he : (2 / ((25*n).factorial : ℚ)^10) = 2 * ((1 / ((25*n).factorial : ℚ))^2)^5 := by
      ring
    rw [he,map_mul]
    ring
  rw [hrew]
  have hA : PolyWeighted p A 0 S := by
    simpa [A,S] using normalizedRising_weighted_allPrimes p (84*n) 1 (-(k : ℤ)) (25*n) (by omega)
  have hB : PolyWeighted p B 0 S := by
    simpa [B,S] using normalizedRising_weighted_allPrimes p (84*n)
      (93*(n : ℤ)+2) (-(k : ℤ)) (25*n) (by omega)
  have hAB : PolyWeighted p ((A*B)^5) 0 S := by
    have h0 : PolyWeighted p (A*B) 0 S := by simpa using polyWeighted_mul hA hB
    have hh : ∀ e : ℕ, PolyWeighted p ((A*B)^e) 0 S := by
      intro e
      induction e with
      | zero => simpa using polyWeighted_one p S
      | succ e ih =>
        rw [pow_succ]
        simpa using polyWeighted_mul ih h0
    exact hh 5
  have hi : 2*i.val ≤ 84*n := by have := i.isLt; unfold fiveRank at this; omega
  have hj : 2*j.val ≤ 84*n := by have := j.isLt; unfold fiveRank at this; omega
  have hpair : PolyWeighted p
      (taylor (x : ℚ) (evenBasis i.val) * taylor (x : ℚ) (evenBasis j.val)) 0 S := by
    simpa [S] using polyWeighted_mul
      (evenBasis_weighted_allPrimes p (84*n) i.val hi x)
      (evenBasis_weighted_allPrimes p (84*n) j.val hj x)
  simpa using polyWeighted_mul
    (polyWeighted_mul
      (polyWeighted_mul (polyWeighted_C (valAtLeast_natCast p 2))
        (polyWeighted_linear_int_slope x S hS)) hAB) hpair

theorem kernelPoleOrder_eq_block_count (n k : ℕ) :
    (∑ b : Fin 12,
      if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (1 : ℕ) else 0) =
      kernelPoleOrder n k := by
  unfold kernelPoleOrder kernelPoleList
  rw [list_count_flatMap, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl; intro b _
  have hmem : k ∈ (List.range (blockLen n b + 1)).map (fun j => blockStart n b + j) ↔
      blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨k - blockStart n b, by omega, by omega⟩
  symm
  change ((List.range (blockLen n b + 1)).map (fun j => blockStart n b + j)).count k = _
  split_ifs with h
  · exact List.count_eq_one_of_mem
      ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
      (hmem.mpr h)
  · exact List.count_eq_zero_of_not_mem (fun hk' => h (hmem.mp hk'))

/-- Exact block-wise factorization of `kernelLocalCofactor n k`. -/
theorem kernelLocalCofactor_eq_block_prod (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    kernelLocalCofactor n k =
      ∏ b : Fin 12,
        ∏ j ∈ (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          (range (blockLen n b + 1)).erase (k - blockStart n b)
        else range (blockLen n b + 1)),
          (X + C (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) := by
  have hden_eq : (X + C (k : ℚ)) ^ kernelPoleOrder n k *
      (∏ a ∈ (kernelPoleSet n).erase k, (X + C (a : ℚ)) ^ kernelPoleOrder n a) =
      denominator n := by
    change _ = kernelDenominator n
    rw [kernel_denominator_powers]
    exact Finset.mul_prod_erase (kernelPoleSet n) (fun a => (X + C (a : ℚ)) ^ kernelPoleOrder n a) hk
  have hblock_split : ∀ b : Fin 12,
      rising (blockStart n b : ℚ) (blockLen n b + 1) =
        (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          X + C (k : ℚ) else 1) *
        ∏ j ∈ (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          (range (blockLen n b + 1)).erase (k - blockStart n b)
        else range (blockLen n b + 1)),
          (X + C ((blockStart n b : ℚ) + (j : ℚ))) := by
    intro b
    unfold rising
    split_ifs with hcond
    · have hmem : k - blockStart n b ∈ range (blockLen n b + 1) := by
        rw [mem_range]; omega
      rw [← Finset.mul_prod_erase _ _ hmem]
      congr 1; congr 1; congr 1
      rw [Nat.cast_sub hcond.1]; ring
    · simp
  have hprod_den : denominator n =
      (X + C (k : ℚ)) ^ kernelPoleOrder n k *
      ∏ b : Fin 12,
        ∏ j ∈ (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          (range (blockLen n b + 1)).erase (k - blockStart n b)
        else range (blockLen n b + 1)),
          (X + C ((blockStart n b : ℚ) + (j : ℚ))) := by
    have h1 : denominator n =
        ∏ b : Fin 12, rising (blockStart n b : ℚ) (blockLen n b + 1) := by
      rfl
    rw [h1]
    have h2 : (∏ b : Fin 12, rising (blockStart n b : ℚ) (blockLen n b + 1)) =
        ∏ b : Fin 12,
          ((if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
            X + C (k : ℚ) else 1) *
          ∏ j ∈ (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
            (range (blockLen n b + 1)).erase (k - blockStart n b)
          else range (blockLen n b + 1)),
            (X + C ((blockStart n b : ℚ) + (j : ℚ)))) :=
      Finset.prod_congr rfl (fun b _ => hblock_split b)
    rw [h2, Finset.prod_mul_distrib]
    congr 1
    have hite : (∏ b : Fin 12,
        if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          X + C (k : ℚ) else 1) =
        ∏ b : Fin 12, (X + C (k : ℚ)) ^
          (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then 1 else 0) :=
      Finset.prod_congr rfl (fun b _ => by split_ifs <;> simp)
    rw [hite, Finset.prod_pow_eq_pow_sum, kernelPoleOrder_eq_block_count]
  have hcancel : (∏ a ∈ (kernelPoleSet n).erase k, (X + C (a : ℚ)) ^ kernelPoleOrder n a) =
      ∏ b : Fin 12,
        ∏ j ∈ (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
          (range (blockLen n b + 1)).erase (k - blockStart n b)
        else range (blockLen n b + 1)),
          (X + C ((blockStart n b : ℚ) + (j : ℚ))) := by
    have hne : (X + C (k : ℚ)) ^ kernelPoleOrder n k ≠ 0 :=
      pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero
    apply mul_left_cancel₀ hne
    rw [hden_eq, hprod_den]
  unfold kernelLocalCofactor
  rw [hcancel, taylor_prod_fin]
  apply Finset.prod_congr rfl; intro b _
  rw [taylor_prod_fin]
  apply Finset.prod_congr rfl; intro j _
  rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
  congr 2; push_cast; ring

/-- Constant-term valuation upper bound & unit-normalized slope for `normLocalCof n k`. -/
theorem normLocalCof_bounds (n p : ℕ) [Fact p.Prime] (_hn : 0 < n) (k : ℕ)
    (hk : k ∈ kernelPoleSet n) :
    (normLocalCof n k).coeff 0 ≠ 0 ∧
    padicValRat p ((normLocalCof n k).coeff 0) ≤
      ((12 - kernelPoleOrder n k : ℕ) : ℤ) * (Nat.log p (84 * n) : ℤ) ∧
    PolyWeighted p (C (1 / (normLocalCof n k).coeff 0) * normLocalCof n k)
      0 (Nat.log p (84 * n)) := by
  let S : ℤ := (Nat.log p (84 * n) : ℤ)
  have hbnd := kernel_pole_address_bounds n k hk
  -- Factor `normLocalCof` per block
  let s_b : Fin 12 → Finset ℕ := fun b =>
    if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then
      (range (blockLen n b + 1)).erase (k - blockStart n b)
    else range (blockLen n b + 1)
  let C_b : Fin 12 → ℚ[X] := fun b =>
    C (1 / ((blockLen n b).factorial : ℚ)) *
      ∏ j ∈ s_b b, (X + C (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
  have hfact : normLocalCof n k = ∏ b : Fin 12, C_b b := by
    unfold normLocalCof
    rw [kernelLocalCofactor_eq_block_prod n k hk]
    have hCprod : C (1 / (∏ b : Fin 12, ((blockLen n b).factorial : ℚ))) =
        ∏ b : Fin 12, C (1 / ((blockLen n b).factorial : ℚ)) := by
      rw [← map_prod]; congr 1
      rw [one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl; intro b _; rw [one_div]
    rw [hCprod, ← Finset.prod_mul_distrib]
  -- Check each block's constant term and normalized weight
  have hblock_info : ∀ b : Fin 12,
      (C_b b).coeff 0 ≠ 0 ∧
      padicValRat p ((C_b b).coeff 0) ≤
        (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then 0 else S) ∧
      PolyWeighted p (C (1 / (C_b b).coeff 0) * C_b b) 0 S := by
    intro b
    have hob : offsets b ≤ 9 := by fin_cases b <;> decide
    have hSb_bounds : 34 * n + 1 ≤ blockStart n b ∧
        blockStart n b + blockLen n b ≤ 84 * n + 1 := by
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
    have hdist : ∀ j ∈ s_b b,
        ((blockStart n b + j : ℤ) - (k : ℤ)) ≠ 0 ∧
        ((blockStart n b + j : ℤ) - (k : ℤ)).natAbs ≤ 84 * n := by
      intro j hj
      dsimp [s_b] at hj
      split_ifs at hj with hcond
      · have hne := (Finset.mem_erase.mp hj).1
        have hlt := mem_range.mp (Finset.mem_erase.mp hj).2
        omega
      · have hlt := mem_range.mp hj
        omega
    have hcoeff0 : (C_b b).coeff 0 =
        (1 / ((blockLen n b).factorial : ℚ)) *
          ∏ j ∈ s_b b, (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) := by
      dsimp [C_b]
      rw [Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_C, eval_prod]
      congr 1
      apply Finset.prod_congr rfl; intro j _; simp
    have hne0 : (C_b b).coeff 0 ≠ 0 := by
      rw [hcoeff0]
      apply mul_ne_zero (one_div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact_mod_cast (hdist j hj).1
    -- Normalized weight of `C (1 / (C_b b).coeff 0) * C_b b`
    have hweight : PolyWeighted p (C (1 / (C_b b).coeff 0) * C_b b) 0 S := by
      have hrew : C (1 / (C_b b).coeff 0) * C_b b =
          ∏ j ∈ s_b b, (1 + C (1 / (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) * X) := by
        dsimp [C_b]
        rw [hcoeff0, ← mul_assoc, ← map_mul]
        have hfac_ne : ((blockLen n b).factorial : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        have hprod_ne : (∏ j ∈ s_b b, (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist j hj).1)
        have hsc : (1 / ((1 / ((blockLen n b).factorial : ℚ)) *
            ∏ j ∈ s_b b, (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))) *
            (1 / ((blockLen n b).factorial : ℚ)) =
            ∏ j ∈ s_b b, (1 / (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const_one]
          field_simp
        rw [hsc, map_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl; intro j hj
        have hne : (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) ≠ 0 := by
          exact_mod_cast (hdist j hj).1
        rw [mul_add, ← map_mul, one_div_mul_cancel hne, map_one, add_comm]
      rw [hrew]
      have hprod := polyWeighted_prod (p := p) (s_b b)
        (fun j => 1 + C (1 / (((blockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) * X)
        (fun _ => 0) S (fun j hj => by
          intro r
          cases r with
          | zero =>
            simp only [coeff_add, coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero,
              Nat.cast_zero, sub_zero]
            exact valAtLeast_one p
          | succ r =>
            cases r with
            | zero =>
              simp only [zero_add, coeff_add, coeff_one, show ¬ (1 : ℕ) = 0 by omega, ite_false,
                zero_add, coeff_C_mul, coeff_X_one, mul_one, Nat.cast_one, zero_sub]
              right
              rw [one_div, padicValRat.inv, padicValRat.of_int, padicValInt]
              have hd := hdist j hj
              have hlog := padicValNat_le_log p (Int.natAbs_pos.mpr hd.1) hd.2
              omega
            | succ r =>
              simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X,
                show ¬ (r + 1 + 1 = 0) by omega, show ¬ (1 = r + 1 + 1) by omega,
                ite_false, mul_zero, add_zero]
              exact valAtLeast_zero p _)
      simpa using hprod
    -- Constant term valuation upper bound
    have hval : padicValRat p ((C_b b).coeff 0) ≤
        if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then 0 else S := by
      let a := blockStart n b
      let L := blockLen n b
      change padicValRat p ((C_b b).coeff 0) ≤ if a ≤ k ∧ k ≤ a + L then 0 else S
      have hfac_ne : (L.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero L
      by_cases hcond : a ≤ k ∧ k ≤ a + L
      · simp only [hcond, and_self, ite_true]
        -- Product equals `(-1)^(k - a) * (k - a)! * (a + L - k)!`
        have hprod_in : (∏ j ∈ (range (L + 1)).erase (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
            (-1 : ℚ) ^ (k - a) * (((k - a).factorial : ℕ) : ℚ) *
              (((a + L - k).factorial : ℕ) : ℚ) := by
          have hsplit : (range (L + 1)).erase (k - a) =
              range (k - a) ∪ Finset.Ico (k - a + 1) (L + 1) := by
            ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
            omega
          have hdisj : Disjoint (range (k - a)) (Finset.Ico (k - a + 1) (L + 1)) := by
            rw [Finset.disjoint_left]; intro j hj1 hj2
            rw [Finset.mem_range] at hj1; rw [Finset.mem_Ico] at hj2; omega
          rw [hsplit, Finset.prod_union hdisj]
          have hleft : (∏ j ∈ range (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (-1 : ℚ) ^ (k - a) * (((k - a).factorial : ℕ) : ℚ) := by
            have hbij : (∏ j ∈ range (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (k - a), (-(((u + 1 : ℕ) : ℚ))) := by
              apply Finset.prod_bij (fun j _ => k - a - 1 - j)
              · intro j hj; exact mem_range.mpr (by have := mem_range.mp hj; omega)
              · intro j₁ hj₁ j₂ hj₂ h; have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega
              · intro u hu; exact ⟨k - a - 1 - u, mem_range.mpr (by have := mem_range.mp hu; omega),
                  by have := mem_range.mp hu; omega⟩
              · intro j hj
                have hjlt := mem_range.mp hj
                have h1 : k - a - 1 - j + 1 = k - a - j := by omega
                rw [h1, Nat.cast_sub (by omega : j ≤ k - a), Nat.cast_sub hcond.1]
                push_cast; ring
            rw [hbij]
            clear hbij hsplit hdisj
            induction (k - a) with
            | zero => simp
            | succ m ihm =>
              rw [Finset.prod_range_succ, ihm, pow_succ, Nat.factorial_succ]
              push_cast; ring
          have hright : (∏ j ∈ Finset.Ico (k - a + 1) (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (((a + L - k).factorial : ℕ) : ℚ) := by
            have hbij : (∏ j ∈ Finset.Ico (k - a + 1) (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (a + L - k), ((u + 1 : ℕ) : ℚ) := by
              apply Finset.prod_bij (fun j _ => j - (k - a + 1))
              · intro j hj; rw [Finset.mem_Ico] at hj; exact mem_range.mpr (by omega)
              · intro j₁ hj₁ j₂ hj₂ h
                rw [Finset.mem_Ico] at hj₁ hj₂; omega
              · intro u hu; rw [mem_range] at hu
                exact ⟨u + (k - a + 1), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro j hj
                rw [Finset.mem_Ico] at hj
                have h1 : j - (k - a + 1) + 1 = a + j - k := by omega
                rw [h1, Nat.cast_sub (by omega : k ≤ a + j)]
                push_cast; ring
            rw [hbij]
            clear hbij hleft hsplit hdisj
            induction (a + L - k) with
            | zero => simp
            | succ m ihm =>
              rw [Finset.prod_range_succ, ihm, Nat.factorial_succ]
              push_cast; ring
          rw [hleft, hright]
        have hC0_eq : (C_b b).coeff 0 =
            (-1 : ℚ) ^ (k - a) / ((L.choose (k - a) : ℕ) : ℚ) := by
          rw [hcoeff0]
          have hs_eq : s_b b = (range (L + 1)).erase (k - a) := by
            change (if a ≤ k ∧ k ≤ a + L then (range (L + 1)).erase (k - a) else range (L + 1)) = _
            simp only [hcond, and_self, ite_true]
          rw [hs_eq, hprod_in]
          have hch : L.choose (k - a) * (k - a).factorial * (a + L - k).factorial = L.factorial := by
            have hsub : L - (k - a) = a + L - k := by omega
            have := Nat.choose_mul_factorial_mul_factorial (show k - a ≤ L by omega)
            rwa [hsub] at this
          have hch_ne : ((L.choose (k - a) : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.choose_pos (show k - a ≤ L by omega)).ne'
          have hchQ : ((L.choose (k - a) : ℕ) : ℚ) * (((k - a).factorial : ℕ) : ℚ) *
              (((a + L - k).factorial : ℕ) : ℚ) = (L.factorial : ℚ) := by
            exact_mod_cast hch
          field_simp
          rw [← hchQ]
          ring
        rw [hC0_eq]
        have h1ne : (-1 : ℚ) ^ (k - a) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hch_ne : ((L.choose (k - a) : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (show k - a ≤ L by omega)).ne'
        have hv1 : padicValRat p ((-1 : ℚ) ^ (k - a)) = 0 := by
          rcases Nat.even_or_odd (k - a) with he | ho
          · rw [he.neg_one_pow, padicValRat.one]
          · rw [ho.neg_one_pow, padicValRat.neg, padicValRat.one]
        rw [padicValRat.div h1ne hch_ne, hv1, zero_sub, padicValRat.of_nat]
        omega
      · simp only [hcond, ↓reduceIte]
        have hs_eq : s_b b = range (L + 1) := by
          change (if a ≤ k ∧ k ≤ a + L then (range (L + 1)).erase (k - a) else range (L + 1)) = _
          simp only [hcond, ↓reduceIte]
        -- Helper: `∏_{j=0}^L (d + j) = (d + L)! / (d - 1)!`
        have hprod_shifted : ∀ d : ℕ, 1 ≤ d →
            (∏ j ∈ range (L + 1), ((d + j : ℕ) : ℚ)) =
              (((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ) := by
          intro d hd1
          have hne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          rw [eq_div_iff hne]
          have hnat : (∏ j ∈ range (L + 1), (d + j)) * (d - 1).factorial = (d + L).factorial := by
            clear hne
            induction L with
            | zero =>
              simp only [zero_add, range_one, prod_singleton, add_zero]
              exact Nat.mul_factorial_pred (by omega : d ≠ 0)
            | succ m ihm =>
              rw [Finset.prod_range_succ]
              have heq : d + (m + 1) = (d + m) + 1 := by omega
              rw [heq, Nat.factorial_succ]
              calc
                (∏ x ∈ range (m + 1), (d + x)) * (d + m + 1) * (d - 1).factorial
                    = (d + m + 1) * ((∏ x ∈ range (m + 1), (d + x)) * (d - 1).factorial) := by ring
                _ = (d + m + 1) * (d + m).factorial := by rw [ihm]
          exact_mod_cast hnat
        rcases (show k < a ∨ a + L < k by omega) with hlt | hgt
        · -- `k < a`: `d = a - k ≥ 1`, `d + L = a + L - k ≤ 50n ≤ 84n`
          let d := a - k
          have hd1 : 1 ≤ d := by omega
          have hdL : d + L ≤ 84 * n := by omega
          have hpeq : (∏ j ∈ s_b b, (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ) := by
            rw [hs_eq, ← hprod_shifted d hd1]
            apply Finset.prod_congr rfl; intro j _
            rw [Nat.cast_add, Nat.cast_sub hlt.le]; push_cast; ring
          rw [hcoeff0, hpeq, one_div, mul_comm, ← div_eq_mul_inv, div_div]
          have hnum_ne : (((d + L).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hden1_ne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          rw [padicValRat.div hnum_ne (mul_ne_zero hden1_ne hfac_ne),
            padicValRat.mul hden1_ne hfac_ne,
            padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
          have hbound := offBlock_factorial_ratio_val_le p d L (84 * n) hd1 hdL
          omega
        · -- `a + L < k`: `d = k - (a + L) ≥ 1`, `d + L = k - a ≤ 50n ≤ 84n`
          let d := k - (a + L)
          have hd1 : 1 ≤ d := by omega
          have hdL : d + L ≤ 84 * n := by omega
          have hpeq : (∏ j ∈ s_b b, (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (-1 : ℚ) ^ (L + 1) *
                ((((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ)) := by
            rw [hs_eq, ← hprod_shifted d hd1]
            have hbij : (∏ j ∈ range (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (L + 1), (-1 : ℚ) * ((d + u : ℕ) : ℚ) := by
              apply Finset.prod_bij (fun j _ => L - j)
              · intro j hj; exact mem_range.mpr (by have := mem_range.mp hj; omega)
              · intro j₁ hj₁ j₂ hj₂ h; have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega
              · intro u hu; exact ⟨L - u, mem_range.mpr (by have := mem_range.mp hu; omega),
                  by have := mem_range.mp hu; omega⟩
              · intro j hj
                have hjL : j ≤ L := Nat.lt_succ_iff.mp (mem_range.mp hj)
                rw [Nat.cast_add, Nat.cast_sub hgt.le, Nat.cast_sub hjL]
                push_cast; ring
            rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          rw [hcoeff0, hpeq]
          have h1ne : (-1 : ℚ) ^ (L + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          have hnum_ne : (((d + L).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hden1_ne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hv1 : padicValRat p ((-1 : ℚ) ^ (L + 1)) = 0 := by
            rcases Nat.even_or_odd (L + 1) with he | ho
            · rw [he.neg_one_pow, padicValRat.one]
            · rw [ho.neg_one_pow, padicValRat.neg, padicValRat.one]
          have hrew : (1 / (L.factorial : ℚ)) *
              ((-1 : ℚ) ^ (L + 1) * ((((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ))) =
              (-1 : ℚ) ^ (L + 1) * ((((d + L).factorial : ℕ) : ℚ) /
                ((((d - 1).factorial : ℕ) : ℚ) * (L.factorial : ℚ))) := by ring
          rw [hrew, padicValRat.mul h1ne (div_ne_zero hnum_ne (mul_ne_zero hden1_ne hfac_ne)),
            hv1, zero_add, padicValRat.div hnum_ne (mul_ne_zero hden1_ne hfac_ne),
            padicValRat.mul hden1_ne hfac_ne,
            padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
          have hbound := offBlock_factorial_ratio_val_le p d L (84 * n) hd1 hdL
          omega
    exact ⟨hne0, hval, hweight⟩
  -- Combine all 14 blocks
  have hC0_prod : (normLocalCof n k).coeff 0 = ∏ b : Fin 12, (C_b b).coeff 0 := by
    rw [hfact, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
    apply Finset.prod_congr rfl; intro b _; rw [Polynomial.coeff_zero_eq_eval_zero]
  have hC0_ne : (normLocalCof n k).coeff 0 ≠ 0 := by
    rw [hC0_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ => (hblock_info b).1)
  have hcount_off : (∑ b : Fin 12,
      if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else S) =
      ((12 - kernelPoleOrder n k : ℕ) : ℤ) * S := by
    have hcount_in := kernelPoleOrder_eq_block_count n k
    have hord := kernel_pole_order_le n k
    have hsum14 : (∑ b : Fin 12,
        ((if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else 1) +
         (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (1 : ℤ) else 0))) =
        (12 : ℤ) := by
      have : ∀ b : Fin 12,
          (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else 1) +
          (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (1 : ℤ) else 0) = 1 := by
        intro b; split_ifs <;> norm_num
      simp [this]
    have hoff1 : (∑ b : Fin 12,
        if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else 1) =
        ((12 - kernelPoleOrder n k : ℕ) : ℤ) := by
      rw [Finset.sum_add_distrib] at hsum14
      have hinZ : (∑ b : Fin 12,
          if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (1 : ℤ) else 0) =
          (kernelPoleOrder n k : ℤ) := by
        have := congrArg (Nat.cast (R := ℤ)) hcount_in
        push_cast at this
        simpa [apply_ite] using this
      rw [Nat.cast_sub hord]
      push_cast at hsum14 ⊢
      linarith
    calc
      (∑ b : Fin 12,
          if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else S)
          = (∑ b : Fin 12,
              (if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else 1) * S) := by
            apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
      _ = (∑ b : Fin 12,
            if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then (0 : ℤ) else 1) * S := by
            rw [← Finset.sum_mul]
      _ = ((12 - kernelPoleOrder n k : ℕ) : ℤ) * S := by rw [hoff1]
  have hC0_val : padicValRat p ((normLocalCof n k).coeff 0) ≤
      ((12 - kernelPoleOrder n k : ℕ) : ℤ) * S := by
    have hpadic_prod : ∀ s : Finset (Fin 12),
        padicValRat p (∏ b ∈ s, (C_b b).coeff 0) = ∑ b ∈ s, padicValRat p ((C_b b).coeff 0) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValRat.mul (hblock_info a).1
            (Finset.prod_ne_zero_iff.mpr (fun b _ => (hblock_info b).1)), ih]
    rw [hC0_prod, hpadic_prod Finset.univ, ← hcount_off]
    exact Finset.sum_le_sum (fun b _ => (hblock_info b).2.1)
  have hnorm_weight : PolyWeighted p
      (C (1 / (normLocalCof n k).coeff 0) * normLocalCof n k) 0 S := by
    have hprod_eq : C (1 / (normLocalCof n k).coeff 0) * normLocalCof n k =
        ∏ b : Fin 12, (C (1 / (C_b b).coeff 0) * C_b b) := by
      rw [hC0_prod, hfact]
      have hC : C (1 / ∏ b : Fin 12, (C_b b).coeff 0) =
          ∏ b : Fin 12, C (1 / (C_b b).coeff 0) := by
        rw [← map_prod]; congr 1
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      rw [hC, ← Finset.prod_mul_distrib]
    rw [hprod_eq]
    simpa using polyWeighted_prod (p := p) (Finset.univ : Finset (Fin 12))
      (fun b => C (1 / (C_b b).coeff 0) * C_b b) (fun _ => 0) S
      (fun b _ => (hblock_info b).2.2)
  exact ⟨hC0_ne, hC0_val, hnorm_weight⟩

/-! ## All-prime-power bounds on principal coefficients, `sixMatrix`, and `sixPrimitiveScalar` -/

theorem kernelPrincipalCoefficients_valAtLeast_allPrimes (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (i j : Fin (fiveRank n)) (k : ℕ) (hk : k ∈ kernelPoleSet n)
    (l : Fin (kernelPoleOrder n k)) :
    ValAtLeast p (-((11 - l.val : ℕ) : ℤ) * (Nat.log p (84 * n) : ℤ))
      (kernelPrincipalCoefficients n i j k l) := by
  let S : ℤ := (Nat.log p (84 * n) : ℤ)
  have hS0 : 0 ≤ S := Int.natCast_nonneg _
  obtain ⟨hC0_ne, hC0_val, hU_wt⟩ := normLocalCof_bounds n p hn k hk
  let U : ℚ[X] := C (1 / (normLocalCof n k).coeff 0) * normLocalCof n k
  let Q : ℚ[X] := C ((normLocalCof n k).coeff 0) * kernelLocalPrincipal n i j k
  have hU0 : U.coeff 0 = 1 := by
    dsimp [U]; rw [coeff_C_mul, one_div_mul_cancel hC0_ne]
  have hdvd : X ^ kernelPoleOrder n k ∣ normLocalNum n i j k - Q * U := by
    have hQU : Q * U = kernelLocalPrincipal n i j k * normLocalCof n k := by
      dsimp [Q, U]
      have h1 : C ((normLocalCof n k).coeff 0) * C (1 / (normLocalCof n k).coeff 0) = 1 := by
        rw [← map_mul, mul_one_div_cancel hC0_ne, map_one]
      calc
        C ((normLocalCof n k).coeff 0) * kernelLocalPrincipal n i j k *
            (C (1 / (normLocalCof n k).coeff 0) * normLocalCof n k)
            = (C ((normLocalCof n k).coeff 0) * C (1 / (normLocalCof n k).coeff 0)) *
                (kernelLocalPrincipal n i j k * normLocalCof n k) := by ring
        _ = _ := by rw [h1, one_mul]
    rw [hQU]
    exact sixNormLocal_congruence n i j k hk
  let q := kernelPoleOrder n k - (l.val + 1)
  have hqm : q < kernelPoleOrder n k := by have := l.isLt; omega
  have hQval := truncated_division_weighted hU0 hU_wt (normLocalNum_weighted n p hn i j k) hdvd q hqm
  have hcoeff : kernelPrincipalCoefficients n i j k l =
      (1 / (normLocalCof n k).coeff 0) * Q.coeff q := by
    dsimp [Q]
    rw [coeff_C_mul, ← mul_assoc, one_div_mul_cancel hC0_ne, one_mul, kernelLocalPrincipal_coeff]
  rw [hcoeff]
  have hinv : ValAtLeast p (-(((12 - kernelPoleOrder n k : ℕ) : ℤ) * S))
      (1 / (normLocalCof n k).coeff 0) := by
    right
    rw [one_div, padicValRat.inv]
    linarith
  have hmul := valAtLeast_mul hinv hQval
  have hord := kernel_pole_order_le n k
  have hl := l.isLt
  have hexp : -((11 - l.val : ℕ) : ℤ) * S ≤
      -(((12 - kernelPoleOrder n k : ℕ) : ℤ) * S) + -(S * (q : ℤ)) := by
    have hsum_nat : (12 - kernelPoleOrder n k) + q = 11 - l.val := by dsimp [q]; omega
    have hsum_int : ((12 - kernelPoleOrder n k : ℕ) : ℤ) + (q : ℤ) = ((11 - l.val : ℕ) : ℤ) := by
      exact_mod_cast hsum_nat
    nlinarith
  exact valAtLeast_mono hmul hexp


private theorem zetaSymbol_formal (p ℓ : ℕ) [Fact p.Prime] :
    FormalValAtLeast p 0 (zetaSymbol ℓ) := by
  unfold zetaSymbol
  apply formalValAtLeast_sum
  intro s _
  split_ifs
  · exact formalValAtLeast_X p s
  · exact formalValAtLeast_zero p 0

theorem Hpoly_entry_coarse (n p : ℕ) [Fact p.Prime] (i j : Fin (fiveRank n)) :
    FormalValAtLeast p (-(16*(Nat.log p (84*n) : ℤ))) (Hpoly n i j) := by
  let S : ℤ := (Nat.log p (84*n) : ℤ)
  have hS : 0 ≤ S := Int.natCast_nonneg _
  have hn : 0<n := by have := i.isLt; unfold fiveRank at this; omega
  unfold Hpoly fiveEntry
  apply formalValAtLeast_sum
  intro k hk
  apply formalValAtLeast_sum
  intro ℓ hℓ
  have hk' : k ∈ kernelPoleSet n := by rwa [kernelPoleSet_eq_poleList]
  have hb := kernel_pole_address_bounds n k hk'
  have hl := mem_Icc.mp hℓ
  have hlo : ℓ-1 < kernelPoleOrder n k := by
    rw [kernelPoleOrder_eq_poleOrder]
    omega
  let l : Fin (kernelPoleOrder n k) := ⟨ℓ-1,hlo⟩
  have haddr : l.val+1 = ℓ := by dsimp [l]; omega
  have hprincipal := kernelPrincipalCoefficients_valAtLeast_allPrimes n p hn i j k hk' l
  have he := localPrincipal_eq n i j k hk' l
  change localPrincipal n k (l.val+1) (evenBasis i) (evenBasis j) = _ at he
  rw [haddr] at he
  rw [he]
  have hr : (0 : ℤ) ≥ -(((ℓ+4 : ℕ) : ℤ)*S) := neg_nonpos.mpr (mul_nonneg (by positivity) hS)
  have hH : FormalValAtLeast p (-(((ℓ+4 : ℕ) : ℤ)*S))
      (zetaSymbol ℓ - MvPolynomial.C (lowerHarmonic (ℓ+4) (k-25*n-1))) := by
    apply formalValAtLeast_sub (formalValAtLeast_mono (zetaSymbol_formal p ℓ) hr)
    apply formalValAtLeast_C
    rw [harmonic_eq]
    exact OddZetaSix.harmonicCutoff_valAtLeast_allPrimes p _ _ (84*n) (by omega)
  have hq := valAtLeast_mul (valAtLeast_natCast p ((ℓ+3).choose 4)) hprincipal
  have hres := formalValAtLeast_C_mul hq hH
  apply formalValAtLeast_mono hres
  have h12 := kernel_pole_order_le n k
  have hu : ((11-l.val : ℕ) : ℤ) + ((ℓ+4 : ℕ) : ℤ) = 16 := by omega
  change -(16*S) ≤ 0 + -((11-l.val : ℕ) : ℤ)*S + -(((ℓ+4 : ℕ) : ℤ)*S)
  nlinarith

theorem content_coarse_bound (n p : ℕ) [Fact p.Prime] :
    -padicValRat p (content n) ≤ 16*(fiveRank n : ℤ)*(Nat.log p (84*n) : ℤ) := by
  let S : ℤ := (Nat.log p (84*n) : ℤ)
  have hdet := formalValAtLeast_det_uniform (Hpoly n) (-(16*S)) (Hpoly_entry_coarse n p)
  have hc := content_padicValRat_ge_of_formal_nonpos n p
    ((fiveRank n : ℤ)* -(16*S))
    (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (neg_nonpos.mpr (by dsimp [S]; positivity)))
    hdet
  change (fiveRank n : ℤ)* -(16*S) ≤ padicValRat p (content n) at hc
  change -padicValRat p (content n) ≤ 16 * (fiveRank n : ℤ) * S
  linarith

theorem content_large_prime_support (n p : ℕ) [Fact p.Prime] (hp : 84*n < p) :
    0 ≤ padicValRat p (content n) := by
  have h := content_coarse_bound n p
  simp only [Nat.log_eq_zero_iff.mpr (Or.inl hp),Nat.cast_zero,mul_zero] at h
  omega

end OddZetaSix.B40a
