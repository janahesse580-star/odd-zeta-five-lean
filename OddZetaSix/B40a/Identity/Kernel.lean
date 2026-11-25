import OddZetaSix.B40a.PolynomialModel
import Mathlib.Tactic

/-! B40a adaptation of the partial-fraction argument in the upstream
OddZetaSix.SixFunctional module. The upstream project is MIT licensed. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators Topology

abbrev kernelNumerator := numerator
abbrev kernelDenominator := denominator
abbrev kernelNormalization := normalization
abbrev kernelOffset := offsets
abbrev kernelRank := fiveRank

theorem offset_le (b : Fin 12) : 2 * offsets b ≤ 50 := by
  fin_cases b <;> decide

def kernelKernel (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C (normalization n) * numerator n) /
    algebraMap ℚ[X] (RatFunc ℚ) (denominator n)

def kernelCenteredMultiplier (n i j : ℕ) : ℚ[X] :=
  (evenBasis i * evenBasis j).comp (X + C (59*(n : ℚ)+1))

def kernelEntry (n i j : ℕ) : RatFunc ℚ :=
  kernelKernel n * algebraMap ℚ[X] (RatFunc ℚ) (kernelCenteredMultiplier n i j)

theorem kernelNumerator_monic (n : ℕ) : (numerator n).Monic :=
  (monic_X_add_C _).mul (((rising_monic _ _).mul (rising_monic _ _)).pow 5)

theorem kernelDenominator_monic (n : ℕ) : (denominator n).Monic := by
  apply monic_prod_of_monic
  intro b _
  exact rising_monic _ _

theorem kernelNumerator_degree (n : ℕ) : (numerator n).natDegree = 250*n+1 := by
  unfold numerator
  have hm := (rising_monic 1 (25*n)).mul (rising_monic (93*(n:ℚ)+2) (25*n))
  rw [(monic_X_add_C (center n : ℚ)).natDegree_mul (hm.pow 5), natDegree_X_add_C,
    hm.natDegree_pow, (rising_monic 1 (25*n)).natDegree_mul (rising_monic _ _),
    rising_degree, rising_degree]
  ring

theorem kernelDenominator_degree (n : ℕ) : (denominator n).natDegree = 500*n+12 := by
  rw [denominator, natDegree_prod_of_monic _ _ (fun b _ => rising_monic _ _)]
  simp only [rising_degree, Fin.sum_univ_succ, Fin.sum_univ_zero, offsets,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  omega

theorem kernelNormalization_ne_zero (n : ℕ) : normalization n ≠ 0 := by
  unfold normalization
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact_mod_cast Nat.factorial_ne_zero _
  · exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (25*n))
theorem kernelKernel_degree (n : ℕ) :
    (kernelKernel n).intDegree = -250 * (n : ℤ) - 11 := by
  have hn : C (kernelNormalization n) * kernelNumerator n ≠ 0 :=
    mul_ne_zero (by simpa using kernelNormalization_ne_zero n) (kernelNumerator_monic n).ne_zero
  have hd := (kernelDenominator_monic n).ne_zero
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hn' : algebraMap ℚ[X] (RatFunc ℚ) (C (kernelNormalization n) * kernelNumerator n) ≠ 0 :=
    by simpa only [map_zero] using hinj.ne hn
  have hd' : algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) ≠ 0 :=
    by simpa only [map_zero] using hinj.ne hd
  rw [kernelKernel, RatFunc.intDegree_div hn' hd', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, natDegree_C_mul (kernelNormalization_ne_zero n),
    kernelNumerator_degree, kernelDenominator_degree]
  push_cast
  ring

theorem kernelKernel_ne_zero (n : ℕ) : kernelKernel n ≠ 0 := by
  intro h
  have hd := kernelKernel_degree n
  rw [h, RatFunc.intDegree_zero] at hd
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  omega

theorem centeredMultiplier_ne_zero (n i j : ℕ) : kernelCenteredMultiplier n i j ≠ 0 := by
  apply comp_X_add_C_ne_zero_iff.mpr
  exact mul_ne_zero (evenBasis_ne_zero i) (evenBasis_ne_zero j)

theorem centeredMultiplier_degree (n i j : ℕ) :
    (kernelCenteredMultiplier n i j).natDegree = 2 * i + 2 * j := by
  rw [kernelCenteredMultiplier, natDegree_comp,
    natDegree_mul (evenBasis_ne_zero i) (evenBasis_ne_zero j),
    evenBasis_natDegree, evenBasis_natDegree, natDegree_X_add_C, mul_one]

theorem matrixEntryKernel_degree (n i j : ℕ) :
    (kernelEntry n i j).intDegree = -250 * (n : ℤ) - 11 + 2 * (i : ℤ) + 2 * (j : ℤ) := by
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hm : algebraMap ℚ[X] (RatFunc ℚ) (kernelCenteredMultiplier n i j) ≠ 0 := by
    simpa only [map_zero] using hinj.ne (centeredMultiplier_ne_zero n i j)
  rw [kernelEntry, RatFunc.intDegree_mul (kernelKernel_ne_zero n) hm,
    kernelKernel_degree, RatFunc.intDegree_polynomial, centeredMultiplier_degree]
  push_cast
  ring

/-- Every B40a entry at rank `40n` has degree at most `-90n - 15`. -/
theorem kernel_entry_degree_bound (n : ℕ) (i j : Fin (kernelRank n)) :
    (kernelEntry n i j).intDegree ≤ -90 * (n : ℤ) - 15 := by
  rw [matrixEntryKernel_degree]
  have hi : i.val < 40 * n := i.isLt
  have hj : j.val < 40 * n := j.isLt
  omega

theorem kernel_entry_degree_le_neg_two (n : ℕ) (i j : Fin (kernelRank n)) :
    (kernelEntry n i j).intDegree ≤ -2 := by
  have hb := kernel_entry_degree_bound n i j
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  omega


theorem kernelNumerator_reflection (n : ℕ) :
    (numerator n).comp (-X - C (118 * (n : ℚ) + 2)) = -numerator n := by
  have hc : (X + C (center n : ℚ)).comp (-X-C (118*(n : ℚ)+2)) =
      -(X + C (center n : ℚ)) := by
    have hh : (center n : ℚ) = 59*(n : ℚ)+1 := by unfold center; push_cast; ring
    rw [hh,add_comp,X_comp,C_comp]
    simp only [map_add,map_mul,map_ofNat,map_one]
    ring
  unfold numerator
  rw [mul_comp,hc,pow_comp]
  have h := rising_pair_reflection (118 * (n : ℚ) + 2) (25*n)
  have hh : 118 * (n : ℚ) + 2 - ((25*n : ℕ) : ℚ) = 93*(n : ℚ)+2 := by push_cast; ring
  rw [hh] at h
  rw [h,neg_mul]
theorem kernelDenominator_block_odd (n : ℕ) (b : Fin 12) :
    Odd ((50 - 2 * kernelOffset b) * n + 1) := by
  have hb : 2*kernelOffset b ≤ 50 := offset_le b
  refine ⟨(25 - kernelOffset b) * n, ?_⟩
  rw [show 50 - 2 * kernelOffset b = 2 * (25 - kernelOffset b) by omega]
  ring

theorem kernelDenominator_block_reflection (n : ℕ) (b : Fin 12) :
    (rising (((34 + kernelOffset b) * n : ℕ) + 1) ((50 - 2 * kernelOffset b) * n + 1)).comp
        (-X - C (118 * (n : ℚ) + 2)) =
      -rising (((34 + kernelOffset b) * n : ℕ) + 1) ((50 - 2 * kernelOffset b) * n + 1) := by
  have hb : 2*kernelOffset b ≤ 50 := offset_le b
  have hstart : 118 * (n : ℚ) + 2 - (((34 + kernelOffset b) * n : ℕ) + 1) -
      (((50 - 2 * kernelOffset b) * n + 1 : ℕ) : ℚ) + 1 =
      (((34 + kernelOffset b) * n : ℕ) + 1) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [rising_reflection, hstart, (kernelDenominator_block_odd n b).neg_one_pow, neg_one_mul]

/-- The 12 odd-length denominator blocks together are reflection-even. -/
theorem kernelDenominator_reflection (n : ℕ) :
    (kernelDenominator n).comp (-X - C (118 * (n : ℚ) + 2)) = kernelDenominator n := by
  unfold kernelDenominator denominator
  rw [Polynomial.prod_comp]
  calc
    _ = ∏ b : Fin 12, -rising (((34 + kernelOffset b) * n : ℕ) + 1)
          ((50 - 2 * kernelOffset b) * n + 1) := by
      apply Finset.prod_congr rfl
      intro b _
      simpa only [kernelOffset,Nat.cast_add,Nat.cast_one] using kernelDenominator_block_reflection n b
    _ = _ := by rw [Finset.prod_neg]; norm_num

/-- `R_n(t)` is strictly odd under `t ↦ -2 c_n - t`. -/
theorem kernelKernel_reflection (n : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ)
        ((C (kernelNormalization n) * kernelNumerator n).comp
          (-X - C (118 * (n : ℚ) + 2))) /
      algebraMap ℚ[X] (RatFunc ℚ)
        ((kernelDenominator n).comp (-X - C (118 * (n : ℚ) + 2))) =
      -kernelKernel n := by
  simp only [mul_comp, C_comp, kernelNumerator_reflection, kernelDenominator_reflection,
    mul_neg, map_neg, neg_div, kernelKernel]

theorem centeredMultiplier_reflection (n i j : ℕ) :
    (kernelCenteredMultiplier n i j).comp (-X - C (118 * (n : ℚ) + 2)) =
      kernelCenteredMultiplier n i j := by
  apply Polynomial.funext
  intro t
  simp only [kernelCenteredMultiplier, eval_comp, eval_mul, eval_add, eval_X, eval_C,
    eval_sub, eval_neg]
  rw [show -t - (118 * (n : ℚ) + 2) + (59 * (n : ℚ) + 1) =
      -(t + (59 * (n : ℚ) + 1)) by ring,
    evenBasis_eval_neg, evenBasis_eval_neg]

theorem matrixEntryKernel_reflection (n i j : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ)
        ((C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j).comp
          (-X - C (118 * (n : ℚ) + 2))) /
      algebraMap ℚ[X] (RatFunc ℚ)
        ((kernelDenominator n).comp (-X - C (118 * (n : ℚ) + 2))) =
      -kernelEntry n i j := by
  rw [mul_comp, centeredMultiplier_reflection, map_mul, mul_div_right_comm,
    kernelKernel_reflection, neg_mul]
  rfl

/-! ## Poles, multiplicities, and unique partial fractions -/

/-- All pole addresses with full multiplicity across the 12 denominator blocks. -/
def kernelPoleList (n : ℕ) : List ℕ :=
  (List.finRange 12).flatMap fun b =>
    (List.range ((50 - 2 * kernelOffset b) * n + 1)).map fun j =>
      (34 + kernelOffset b) * n + 1 + j

def kernelPoleSet (n : ℕ) : Finset ℕ := (kernelPoleList n).toFinset

def kernelPoleOrder (n k : ℕ) : ℕ := (kernelPoleList n).count k

private theorem list_flatMap_map_prod {α M : Type*} [CommMonoid M]
    (l : List α) (f : α → List ℕ) (g : ℕ → M) :
    ((l.flatMap f).map g).prod = (l.map fun b => ((f b).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

private theorem range_map_prod_eq {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ → M) :
    ((List.range m).map f).prod = ∏ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.prod_range_succ, ih]

private theorem finRange_map_prod_eq {M : Type*} [CommMonoid M] (m : ℕ) (f : Fin m → M) :
    ((List.finRange m).map f).prod = ∏ b : Fin m, f b := by
  rw [← Fin.prod_univ_def]

theorem kernel_denominator_list (n : ℕ) :
    kernelDenominator n = ((kernelPoleList n).map fun k : ℕ => X + C (k : ℚ)).prod := by
  simp only [kernelPoleList, list_flatMap_map_prod, List.map_map, Function.comp_def]
  simp only [range_map_prod_eq, finRange_map_prod_eq]
  unfold kernelDenominator denominator rising
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  push_cast
  ring

theorem kernel_denominator_powers (n : ℕ) :
    kernelDenominator n = ∏ k ∈ kernelPoleSet n, (X + C (k : ℚ)) ^ (kernelPoleOrder n k) := by
  rw [kernel_denominator_list, Finset.prod_list_map_count (kernelPoleList n)
    (fun k : ℕ => X + C (k : ℚ))]
  rfl

theorem kernel_pole_address_bounds (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    34 * n + 1 ≤ k ∧ k ≤ 84 * n + 1 := by
  simp only [kernelPoleSet, List.mem_toFinset, kernelPoleList, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map, List.mem_range] at hk
  obtain ⟨b, j, hj, rfl⟩ := hk
  have hb : 2*kernelOffset b ≤ 50 := offset_le b
  have hsub : 50 - 2 * kernelOffset b + 2 * kernelOffset b = 50 := by omega
  constructor <;> nlinarith

theorem kernel_pole_order_positive (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    0 < kernelPoleOrder n k := by
  simpa only [kernelPoleOrder, kernelPoleSet, List.mem_toFinset] using
    (List.count_pos_iff.mpr (List.mem_toFinset.mp hk))

theorem kernel_pole_order_le (n k : ℕ) : kernelPoleOrder n k ≤ 12 := by
  unfold kernelPoleOrder kernelPoleList
  rw [list_count_flatMap]
  have hb (b : Fin 12) :
      ((List.range ((50 - 2 * kernelOffset b) * n + 1)).map
        fun j => (34 + kernelOffset b) * n + 1 + j).count k ≤ 1 := by
    apply List.nodup_iff_count_le_one.mp
    apply (List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr
    exact List.nodup_range
  calc
    _ ≤ ((List.finRange 12).map fun _ => 1).sum := List.sum_le_sum (fun b _ => hb b)
    _ = 12 := by decide

theorem kernel_pole_factors_coprime (n : ℕ) :
    Set.Pairwise (kernelPoleSet n : Set ℕ) (fun k l : ℕ =>
      IsCoprime (X + C (k : ℚ)) (X + C (l : ℚ))) := by
  intro k _ l _ hkl
  have hinj : Function.Injective (fun j : ℕ => -(j : ℚ)) := by
    intro a b h
    exact_mod_cast neg_injective h
  simpa only [C_neg, sub_neg_eq_add] using
    (Polynomial.pairwise_coprime_X_sub_C hinj hkl)

private theorem constant_of_degree_lt_one (p : ℚ[X]) (hp : p.degree < 1) :
    p = C (p.coeff 0) := by
  have hcoeff := (degree_lt_iff_coeff_zero p 1).mp hp
  ext j
  by_cases hj : j = 0
  · simp [hj]
  · simp [coeff_C, hj, hcoeff j (by omega)]

def kernelPrincipalTerm (k l : ℕ) (a : ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C a) /
    algebraMap ℚ[X] (RatFunc ℚ) ((X + C (k : ℚ)) ^ (l + 1))

theorem kernel_partial_fractions (n : ℕ) (i j : Fin (kernelRank n)) :
    ∃ b : (k : ℕ) → Fin (kernelPoleOrder n k) → ℚ,
      kernelEntry n i j =
        ∑ k ∈ kernelPoleSet n, ∑ l, kernelPrincipalTerm k l.val (b k l) := by
  let f := C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j
  let g : ℕ → ℚ[X] := fun k => X + C (k : ℚ)
  let gi : ℕ → RatFunc ℚ := fun k => (algebraMap ℚ[X] (RatFunc ℚ) (g k))⁻¹
  have hgi (k : ℕ) (_hk : k ∈ kernelPoleSet n) :
      gi k * algebraMap ℚ[X] (RatFunc ℚ) (g k) = 1 := by
    apply inv_mul_cancel₀
    have hz := (monic_X_add_C (k : ℚ)).ne_zero
    simpa only [map_zero, g] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne hz
  obtain ⟨q, r, hr, heq⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse f
      (fun k (_ : k ∈ kernelPoleSet n) => monic_X_add_C (k : ℚ))
      (kernel_pole_factors_coprime n) (kernelPoleOrder n) hgi
  let b : (k : ℕ) → Fin (kernelPoleOrder n k) → ℚ := fun k l => (r k l).coeff 0
  have hconstant (k : ℕ) (hk : k ∈ kernelPoleSet n) (l : Fin (kernelPoleOrder n k)) :
      r k l = C (b k l) := by
    apply constant_of_degree_lt_one
    simpa only [degree_X_add_C] using hr k hk l
  have hprod : (∏ k ∈ kernelPoleSet n, gi k ^ kernelPoleOrder n k) =
      (algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n))⁻¹ := by
    rw [kernel_denominator_powers, map_prod]
    simp only [gi, g, map_pow, Finset.prod_inv_distrib, inv_pow]
  have hleft : algebraMap ℚ[X] (RatFunc ℚ) f *
      ∏ k ∈ kernelPoleSet n, gi k ^ kernelPoleOrder n k = kernelEntry n i j := by
    rw [hprod]
    simp only [f, map_mul, kernelEntry, kernelKernel, div_eq_mul_inv]
    ring
  have hsum : (∑ k ∈ kernelPoleSet n, ∑ l,
      algebraMap ℚ[X] (RatFunc ℚ) (r k l) * gi k ^ (l.val + 1)) =
      ∑ k ∈ kernelPoleSet n, ∑ l, kernelPrincipalTerm k l.val (b k l) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l _
    rw [hconstant k hk l]
    simp only [kernelPrincipalTerm, gi, g, div_eq_mul_inv, map_pow, inv_pow]
  rw [hleft, hsum] at heq
  have hf : StrictlyProper (kernelEntry n i j) := Or.inr (by
    have hdeg := kernel_entry_degree_le_neg_two n i j
    omega)
  have hs : StrictlyProper (∑ k ∈ kernelPoleSet n, ∑ l,
      kernelPrincipalTerm k l.val (b k l)) := by
    apply strictlyProper_sum
    intro k _
    apply strictlyProper_sum
    intro l _
    exact strictlyProper_principal _ _ _
  have hq := quotient_eq_zero_of_strictlyProper _ _ _ hf hs heq
  exact ⟨b, by simpa only [hq, map_zero, zero_add] using heq⟩

def kernelPrincipalCoefficients (n : ℕ) (i j : Fin (kernelRank n)) :
    (k : ℕ) → Fin (kernelPoleOrder n k) → ℚ :=
  Classical.choose (kernel_partial_fractions n i j)

theorem kernelPrincipalCoefficients_spec (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelEntry n i j = ∑ k ∈ kernelPoleSet n, ∑ l,
      kernelPrincipalTerm k l.val (kernelPrincipalCoefficients n i j k l) :=
  Classical.choose_spec (kernel_partial_fractions n i j)

theorem kernel_principal_coefficients_unique (n : ℕ)
    (a b : (k : ℕ) → Fin (kernelPoleOrder n k) → ℚ)
    (h : (∑ k ∈ kernelPoleSet n, ∑ l, kernelPrincipalTerm k l.val (a k l)) =
      ∑ k ∈ kernelPoleSet n, ∑ l, kernelPrincipalTerm k l.val (b k l)) :
    ∀ k ∈ kernelPoleSet n, a k = b k := by
  let gi : ℕ → RatFunc ℚ := fun k =>
    (algebraMap ℚ[X] (RatFunc ℚ) (X + C (k : ℚ)))⁻¹
  have hgi (k : ℕ) (_hk : k ∈ kernelPoleSet n) :
      gi k * algebraMap ℚ[X] (RatFunc ℚ) (X + C (k : ℚ)) = 1 := by
    apply inv_mul_cancel₀
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (monic_X_add_C (k : ℚ)).ne_zero
  have hc (c : ℚ) (k : ℕ) : (C c).degree < (X + C (k : ℚ)).degree :=
    degree_C_le.trans_lt (by rw [degree_X_add_C]; norm_num)
  have heq : algebraMap ℚ[X] (RatFunc ℚ) 0 +
      (∑ k ∈ kernelPoleSet n, ∑ l, algebraMap ℚ[X] (RatFunc ℚ) (C (a k l)) *
        gi k ^ (l.val + 1)) = algebraMap ℚ[X] (RatFunc ℚ) 0 +
      ∑ k ∈ kernelPoleSet n, ∑ l, algebraMap ℚ[X] (RatFunc ℚ) (C (b k l)) *
        gi k ^ (l.val + 1) := by
    simpa only [map_zero, zero_add, kernelPrincipalTerm, gi, div_eq_mul_inv,
      map_pow, inv_pow] using h
  have hu := quo_add_sum_rem_mul_pow_inverse_unique
    (fun k (_ : k ∈ kernelPoleSet n) => monic_X_add_C (k : ℚ))
    (kernel_pole_factors_coprime n) hgi (fun k _ l => hc (a k l) k)
      (fun k _ l => hc (b k l) k) heq
  intro k hk
  funext l
  have hl := congrArg (fun f : Fin (kernelPoleOrder n k) → ℚ[X] => (f l).coeff 0)
    (hu.2 k hk)
  simpa using hl

/-! ## Cleared polynomial identity and simple-residue cancellation (`ζ(5)` = 0) -/

def kernelPoleComplement (n k l : ℕ) : ℚ[X] :=
  (X + C (k : ℚ)) ^ (kernelPoleOrder n k - (l + 1)) *
    ∏ a ∈ (kernelPoleSet n).erase k, (X + C (a : ℚ)) ^ (kernelPoleOrder n a)

theorem kernelPoleComplement_monic (n k l : ℕ) : (kernelPoleComplement n k l).Monic := by
  apply ((monic_X_add_C _).pow _).mul
  apply monic_prod_of_monic
  intro a _
  exact (monic_X_add_C _).pow _

theorem kernelPoleComplement_mul (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) :
    (X + C (k : ℚ)) ^ (l + 1) * kernelPoleComplement n k l = kernelDenominator n := by
  rw [kernelPoleComplement, ← mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega)]
  exact (Finset.mul_prod_erase (kernelPoleSet n)
    (fun a : ℕ => (X + C (a : ℚ)) ^ (kernelPoleOrder n a)) hk).trans
      (kernel_denominator_powers n).symm

theorem kernelPoleComplement_degree (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) :
    (kernelPoleComplement n k l).natDegree + (l + 1) = 500 * n + 12 := by
  have h := congrArg Polynomial.natDegree (kernelPoleComplement_mul n k l hk hl)
  rw [natDegree_mul ((monic_X_add_C _).pow _).ne_zero
    (kernelPoleComplement_monic n k l).ne_zero,
    (monic_X_add_C _).natDegree_pow, natDegree_X_add_C, mul_one,
    kernelDenominator_degree] at h
  omega

theorem kernelPrincipalTerm_clear (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) (a : ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) * kernelPrincipalTerm k l a =
      algebraMap ℚ[X] (RatFunc ℚ) (C a * kernelPoleComplement n k l) := by
  have hne : algebraMap ℚ[X] (RatFunc ℚ) ((X + C (k : ℚ)) ^ (l + 1)) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      ((monic_X_add_C (k : ℚ)).pow (l + 1)).ne_zero
  rw [← kernelPoleComplement_mul n k l hk hl]
  simp only [map_mul, kernelPrincipalTerm]
  field_simp

theorem kernel_cleared_partial_fractions (n : ℕ) (i j : Fin (kernelRank n)) :
    C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j =
      ∑ k ∈ kernelPoleSet n, ∑ l,
        C (kernelPrincipalCoefficients n i j k l) * kernelPoleComplement n k l.val := by
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have h := congrArg (fun f : RatFunc ℚ =>
    algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) * f)
      (kernelPrincipalCoefficients_spec n i j)
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (kernelDenominator_monic n).ne_zero
  simp only [Finset.mul_sum] at h
  have heach : (∑ k ∈ kernelPoleSet n, ∑ l,
      algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) *
      kernelPrincipalTerm k l.val (kernelPrincipalCoefficients n i j k l)) =
      algebraMap ℚ[X] (RatFunc ℚ) (∑ k ∈ kernelPoleSet n, ∑ l,
        C (kernelPrincipalCoefficients n i j k l) * kernelPoleComplement n k l.val) := by
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l _
    exact kernelPrincipalTerm_clear n k l.val hk l.isLt _
  rw [heach] at h
  calc
    _ = algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) * kernelEntry n i j := by
      simp only [kernelEntry, kernelKernel, map_mul]
      field_simp
    _ = _ := h

theorem kernelPoleComplement_top_coeff (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) :
    (kernelPoleComplement n k l).coeff (500 * n + 11) = if l = 0 then 1 else 0 := by
  have hd := kernelPoleComplement_degree n k l hk hl
  by_cases hl0 : l = 0
  · rw [ite_eq_left_iff.mpr (fun h => (h hl0).elim)]
    have he : (kernelPoleComplement n k l).natDegree = 500 * n + 11 := by omega
    rw [← he]
    exact (kernelPoleComplement_monic n k l).coeff_natDegree
  · rw [ite_eq_right_iff.mpr (fun h => (hl0 h).elim)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem kernel_entry_numerator_top_coeff (n : ℕ) (i j : Fin (kernelRank n)) :
    (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j).coeff
      (500 * n + 11) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_mul
    (mul_ne_zero (by simpa using kernelNormalization_ne_zero n) (kernelNumerator_monic n).ne_zero)
    (centeredMultiplier_ne_zero n i j), natDegree_C_mul (kernelNormalization_ne_zero n),
    kernelNumerator_degree, centeredMultiplier_degree]
  have hi : i.val < 40 * n := i.isLt
  have hj : j.val < 40 * n := j.isLt
  omega

/-- The sum of all simple-pole residues vanishes, eliminating the `ζ(5)` term. -/
theorem kernel_residue_sum_zero (n : ℕ) (i j : Fin (kernelRank n)) :
    (∑ k ∈ kernelPoleSet n, ∑ l,
      if l.val = 0 then kernelPrincipalCoefficients n i j k l else 0) = 0 := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (500 * n + 11))
    (kernel_cleared_partial_fractions n i j)
  rw [kernel_entry_numerator_top_coeff] at h
  simp only [finsetSum_coeff, coeff_C_mul] at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [kernelPoleComplement_top_coeff n k l.val hk l.isLt]
  split_ifs <;> simp

/-! ## Real evaluation, `O(t^{-2})` decay at infinity, and fourth-derivative functional -/

/-- Real evaluation of `R_n(x) E_i(x + c_n) E_j(x + c_n)`. -/
def kernelEntryReal (n i j : ℕ) (x : ℝ) : ℝ :=
  aeval x (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j) /
    aeval x (kernelDenominator n)

theorem kernel_pole_translate_pos (n k : ℕ) (hk : k ∈ kernelPoleSet n)
    (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) : 0 < x + (k : ℝ) := by
  have hb := (kernel_pole_address_bounds n k hk).1
  have hb' : 34 * (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hb
  linarith

theorem kernel_denominator_eval_pos (n : ℕ) (x : ℝ)
    (hx : -(34 * (n : ℝ) + 1) < x) : 0 < aeval x (kernelDenominator n) := by
  rw [kernel_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast]
  exact Finset.prod_pos fun k hk => pow_pos (kernel_pole_translate_pos n k hk x hx) _

theorem kernelPoleComplement_eval (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) :
    aeval x (kernelPoleComplement n k l) =
      aeval x (kernelDenominator n) / (x + (k : ℝ)) ^ (l + 1) := by
  have h := congrArg (fun P : ℚ[X] => aeval x P) (kernelPoleComplement_mul n k l hk hl)
  simp only [map_mul, map_pow, map_add, aeval_X, map_natCast] at h
  exact (eq_div_iff (pow_ne_zero _ (ne_of_gt (kernel_pole_translate_pos n k hk x hx)))).mpr
    (by simpa only [mul_comm] using h)

theorem kernelEntryReal_partial_fractions (n : ℕ) (i j : Fin (kernelRank n))
    (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) :
    kernelEntryReal n i j x = ∑ k ∈ kernelPoleSet n, ∑ l,
      (kernelPrincipalCoefficients n i j k l : ℝ) / (x + (k : ℝ)) ^ (l.val + 1) := by
  unfold kernelEntryReal
  rw [kernel_cleared_partial_fractions]
  simp only [map_sum, map_mul, aeval_C, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [kernelPoleComplement_eval n k l.val hk l.isLt x hx]
  have hd := ne_of_gt (kernel_denominator_eval_pos n x hx)
  have hp := pow_ne_zero (l.val + 1) (ne_of_gt (kernel_pole_translate_pos n k hk x hx))
  field_simp
  simp

/-- Explicit `O(t^{-2})` decay at `+∞` for every matrix-entry kernel `R_n(t) E_i(t+c_n) E_j(t+c_n)`. -/
theorem kernel_summation_point_in_halfline (n v : ℕ) :
    -(34 * (n : ℝ) + 1) < (v : ℝ) - 25 * (n : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  linarith

theorem kernelEntryReal_eventuallyEq_partial_fractions (n : ℕ) (i j : Fin (kernelRank n))
    (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) :
    kernelEntryReal n i j =ᶠ[𝓝 x]
      (fun t : ℝ => ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) / (t + (k : ℝ)) ^ (l.val + 1)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
  exact kernelEntryReal_partial_fractions n i j t ht

/-- The normalized fourth derivative `(R_n E_i E_j)^{(4)}(x) / 4!` on the open half-line. -/
theorem kernelEntryReal_fourthDerivative (n : ℕ) (i j : Fin (kernelRank n))
    (x : ℝ) (hx : -(34 * (n : ℝ) + 1) < x) :
    iteratedDeriv 4 (kernelEntryReal n i j) x / 24 =
      ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          (x + (k : ℝ)) ^ (l.val + 5) := by
  have hsmooth (k : ℕ) (hk : k ∈ kernelPoleSet n) :
      ContDiffAt ℝ 4 (fun t : ℝ => ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) / (t + (k : ℝ)) ^ (l.val + 1)) x := by
    apply ContDiffAt.sum
    intro l _
    exact contDiffAt_const_div_pow_add 4 (l.val + 1)
      (kernelPrincipalCoefficients n i j k l : ℝ) x (k : ℝ)
      (ne_of_gt (kernel_pole_translate_pos n k hk x hx))
  rw [Filter.EventuallyEq.iteratedDeriv_eq 4
    (kernelEntryReal_eventuallyEq_partial_fractions n i j x hx)]
  rw [iteratedDeriv_fun_sum hsmooth, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    fourthDerivative_finset_sum (Finset.univ : Finset (Fin (kernelPoleOrder n k)))
      (fun l => (kernelPrincipalCoefficients n i j k l : ℝ))
      (fun _ => (k : ℝ)) (fun l => l.val + 1) x
      (fun _ _ => by omega)
      (fun _ _ => ne_of_gt (kernel_pole_translate_pos n k hk x hx))

theorem kernelEntryReal_fourthDerivative_at_index (n : ℕ) (i j : Fin (kernelRank n)) (v : ℕ) :
    iteratedDeriv 4 (kernelEntryReal n i j) ((v : ℝ) - 25 * (n : ℝ)) / 24 =
      ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          ((v : ℝ) - 25 * (n : ℝ) + (k : ℝ)) ^ (l.val + 5) :=
  kernelEntryReal_fourthDerivative n i j _ (kernel_summation_point_in_halfline n v)

/-- Summation of the normalized fourth derivative from `t = -40 n` to `+∞`. -/
theorem hasSum_five_shifted_inv_pow (n k i : ℕ) (hk : 25*n < k) :
    HasSum (fun v : ℕ => 1 / ((v : ℝ) - 25*(n : ℝ) + k) ^ (i+4))
      (zetaNat (i+4) - (harmonicCutoff (i+4) (k-25*n-1) : ℝ)) := by
  have heq (v : ℕ) : (v : ℝ) - 25*(n : ℝ) + k = (v : ℝ) + ((k-25*n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk.le]
    push_cast
    ring
  simpa only [heq] using (hasSum_shifted_inv_pow (s := i+4) (q := k-25*n)
    (by omega) (by omega))

theorem hasSum_kernel_fourthDerivative (n : ℕ) (i j : Fin (kernelRank n)) :
    HasSum (fun v : ℕ =>
      iteratedDeriv 4 (kernelEntryReal n i j) ((v : ℝ) - 25 * (n : ℝ)) / 24)
      (∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 25 * n - 1) : ℝ))) := by
  have hterm (k : ℕ) (hk : k ∈ kernelPoleSet n) (l : Fin (kernelPoleOrder n k)) :
      HasSum (fun v : ℕ =>
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          ((v : ℝ) - 25 * (n : ℝ) + (k : ℝ)) ^ (l.val + 5))
        ((kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 25 * n - 1) : ℝ))) := by
    have hkstart : 25 * n < k := by
      have := (kernel_pole_address_bounds n k hk).1
      omega
    simpa only [Nat.add_assoc, Nat.reduceAdd, div_eq_mul_inv, one_mul] using
      (hasSum_five_shifted_inv_pow n k (l.val + 1) hkstart).mul_left
        ((kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ))
  have hsum := hasSum_sum (fun k hk => hasSum_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin (kernelPoleOrder n k)))) => hterm k hk l))
  exact hsum.congr_fun (kernelEntryReal_fourthDerivative_at_index n i j)

theorem summable_kernel_fourthDerivative (n : ℕ) (i j : Fin (kernelRank n)) :
    Summable (fun v : ℕ =>
      iteratedDeriv 4 (kernelEntryReal n i j) ((v : ℝ) - 25 * (n : ℝ)) / 24) :=
  (hasSum_kernel_fourthDerivative n i j).summable

/-- The actual six-value determinant matrix entry `(𝓗_n(ζ))_{ij}`. -/
def kernelFunctional (n : ℕ) (i j : Fin (kernelRank n)) : ℝ :=
  ∑' v : ℕ, iteratedDeriv 4 (kernelEntryReal n i j) ((v : ℝ) - 25 * (n : ℝ)) / 24

theorem kernelFunctional_eq_pole_sum (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelFunctional n i j =
      ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 25 * n - 1) : ℝ)) :=
  (hasSum_kernel_fourthDerivative n i j).tsum_eq


end OddZetaSix.B40a
