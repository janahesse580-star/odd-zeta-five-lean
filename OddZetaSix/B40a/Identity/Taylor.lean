import OddZetaSix.B40a.Identity.Parity

/-! Identify the existing Taylor recurrence with the unique partial fractions. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

def kernelLocalPrincipal (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ) : ℚ[X] :=
  ∑ l : Fin (kernelPoleOrder n k),
    monomial (kernelPoleOrder n k - (l.val + 1)) (kernelPrincipalCoefficients n i j k l)

def kernelLocalCofactor (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (∏ a ∈ (kernelPoleSet n).erase k,
    (X + C (a : ℚ)) ^ kernelPoleOrder n a)

def kernelLocalNumerator (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ))
    (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i.val j.val)

theorem taylor_at_negative_linear (k : ℕ) :
    taylor (-(k : ℚ)) (X + C (k : ℚ)) = X := by
  simp only [map_add, taylor_X, taylor_C, add_assoc, ← C_add, neg_add_cancel,
    C_0, add_zero]

private theorem shifted_other_complement_dvd (n k a l : ℕ)
    (hk : k ∈ kernelPoleSet n) (hak : a ≠ k) :
    X ^ kernelPoleOrder n k ∣ taylor (-(k : ℚ)) (kernelPoleComplement n a l) := by
  have hmem : k ∈ (kernelPoleSet n).erase a := mem_erase.mpr ⟨Ne.symm hak, hk⟩
  have hprod := Finset.dvd_prod_of_mem
    (fun b : ℕ => (X + C (b : ℚ)) ^ kernelPoleOrder n b) hmem
  have hdiv : (X + C (k : ℚ)) ^ kernelPoleOrder n k ∣ kernelPoleComplement n a l :=
    dvd_mul_of_dvd_right hprod _
  have h := (taylorAlgHom (-(k : ℚ))).toRingHom.map_dvd hdiv
  change taylor (-(k : ℚ)) ((X + C (k : ℚ)) ^ kernelPoleOrder n k) ∣
    taylor (-(k : ℚ)) (kernelPoleComplement n a l) at h
  simpa only [taylor_pow, taylor_at_negative_linear] using h

private theorem shifted_own_block (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ) :
    (∑ l : Fin (kernelPoleOrder n k), taylor (-(k : ℚ))
      (C (kernelPrincipalCoefficients n i j k l) * kernelPoleComplement n k l.val)) =
      kernelLocalPrincipal n i j k * kernelLocalCofactor n k := by
  simp only [kernelLocalPrincipal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  simp only [kernelPoleComplement, taylor_mul, taylor_C, taylor_pow,
    taylor_at_negative_linear, kernelLocalCofactor, ← C_mul_X_pow_eq_monomial]
  ring

theorem kernelLocalPrincipal_congruence (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ)
    (hk : k ∈ kernelPoleSet n) :
    X ^ kernelPoleOrder n k ∣
      kernelLocalNumerator n i j k -
        kernelLocalPrincipal n i j k * kernelLocalCofactor n k := by
  have he := congrArg (taylor (-(k : ℚ))) (kernel_cleared_partial_fractions n i j)
  simp only [map_sum] at he
  rw [← Finset.sum_erase_add _ _ hk, shifted_own_block] at he
  change X ^ kernelPoleOrder n k ∣
    taylor (-(k : ℚ)) (C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i.val j.val) - _
  rw [he, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro a ha
  apply Finset.dvd_sum
  intro l _
  rw [taylor_mul, taylor_C]
  exact dvd_mul_of_dvd_right (shifted_other_complement_dvd n k a l.val hk (mem_erase.mp ha).1) _

theorem kernelLocalPrincipal_coeff (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ)
    (l : Fin (kernelPoleOrder n k)) :
    (kernelLocalPrincipal n i j k).coeff (kernelPoleOrder n k - (l.val + 1)) =
      kernelPrincipalCoefficients n i j k l := by
  unfold kernelLocalPrincipal
  rw [finsetSum_coeff, Finset.sum_eq_single l]
  · simp
  · intro b _ hbl
    rw [coeff_monomial]
    have hne : kernelPoleOrder n k - (b.val + 1) ≠ kernelPoleOrder n k - (l.val + 1) := by
      have hb := b.isLt; have hl := l.isLt
      intro h; exact hbl (Fin.ext (by omega))
    simp [hne]
  · intro h; exact (h (mem_univ l)).elim


theorem kernelPoleList_eq_poleList (n : ℕ) : kernelPoleList n = poleList n := by
  simp only [kernelPoleList, poleList, List.ofFn_eq_map, List.flatMap_map,
    kernelOffset]

theorem kernelPoleOrder_eq_poleOrder (n k : ℕ) :
    kernelPoleOrder n k = poleOrder n k := by
  rw [kernelPoleOrder, poleOrder, kernelPoleList_eq_poleList]

theorem kernelPoleSet_eq_poleList (n : ℕ) : kernelPoleSet n = (poleList n).toFinset := by
  rw [kernelPoleSet, kernelPoleList_eq_poleList]

private theorem list_prod_extract_count (l : List ℕ) (k : ℕ) (f : ℕ → ℚ[X]) :
    (l.map f).prod = f k ^ l.count k * ((l.filter (· ≠ k)).map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = k
    · subst a
      simp [ih, pow_succ, mul_assoc, mul_left_comm]
    · simp [ih,h,mul_left_comm]

theorem regularDenominator_eq_erase (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    regularDenominator n k =
      ∏ a ∈ (kernelPoleSet n).erase k, (X + C (a : ℚ)) ^ kernelPoleOrder n a := by
  apply mul_left_cancel₀ ((monic_X_add_C (k : ℚ)).pow (kernelPoleOrder n k)).ne_zero
  calc
    _ = denominator n := by
      change _ = kernelDenominator n
      rw [kernel_denominator_list, kernelPoleList_eq_poleList,
        list_prod_extract_count (poleList n) k (fun a => X + C (a : ℚ))]
      rw [regularDenominator,kernelPoleOrder_eq_poleOrder,poleOrder]
    _ = _ := by
      change kernelDenominator n = _
      rw [kernel_denominator_powers]
      exact (Finset.mul_prod_erase _ _ hk).symm

theorem kernelLocalCofactor_ne_zero_coeff (n k : ℕ) :
    (kernelLocalCofactor n k).coeff 0 ≠ 0 := by
  rw [kernelLocalCofactor, taylor_coeff_zero, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  have hne : a ≠ k := (mem_erase.mp ha).1
  simp only [eval_pow,eval_add,eval_X,eval_C]
  apply pow_ne_zero
  intro hz
  apply hne
  exact_mod_cast (show (a : ℚ) = k by linarith)

/-- Any truncated polynomial quotient with a unit constant term follows
the same coefficient recurrence as the original B40a input. -/
theorem localQuotient_eq_coeff_of_congruence (A D Q : ℚ[X])
    (hD : D.coeff 0 ≠ 0) (M : ℕ) (h : X ^ M ∣ A - D * Q) :
    ∀ d < M, localQuotient A D d = Q.coeff d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hc := (Polynomial.X_pow_dvd_iff.mp h) d hd
    rw [coeff_sub,sub_eq_zero,mul_comm D,coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Q.coeff i * D.coeff j),
      Finset.sum_range_succ,Nat.sub_self,← Fin.sum_univ_eq_sum_range] at hc
    rw [localQuotient]
    apply (div_eq_iff hD).2
    have hh : (∑ i : Fin d, D.coeff (d-i.val) * localQuotient A D i.val) =
        ∑ i : Fin d, Q.coeff i.val * D.coeff (d-i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i.val i.isLt (i.isLt.trans hd),mul_comm]
    rw [hh]
    linarith only [hc]

theorem localPrincipal_eq (n : ℕ) (i j : Fin (fiveRank n)) (k : ℕ)
    (hk : k ∈ kernelPoleSet n) (l : Fin (kernelPoleOrder n k)) :
    localPrincipal n k (l.val+1) (evenBasis i) (evenBasis j) =
      kernelPrincipalCoefficients n i j k l := by
  have hd : kernelPoleOrder n k - (l.val+1) < kernelPoleOrder n k := by
    have := l.isLt
    omega
  let A := kernelLocalNumerator n i j k
  let D := kernelLocalCofactor n k
  let Q := kernelLocalPrincipal n i j k
  have hmod : X ^ kernelPoleOrder n k ∣ A - D * Q := by
    simpa [A,D,Q,mul_comm] using kernelLocalPrincipal_congruence n i j k hk
  have h := localQuotient_eq_coeff_of_congruence A D Q
    (kernelLocalCofactor_ne_zero_coeff n k) _ hmod _ hd
  have hc : (center n : ℚ) = 59*(n : ℚ)+1 := by unfold center; push_cast; ring
  rw [localPrincipal, regularDenominator_eq_erase n k hk, ← kernelPoleOrder_eq_poleOrder,
    hc]
  exact h.trans (kernelLocalPrincipal_coeff n i j k l)

end OddZetaSix.B40a
