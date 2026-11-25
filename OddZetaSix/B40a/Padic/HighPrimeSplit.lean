import OddZetaSix.B40a.Identity.Evaluation
import OddZetaSix.SixGateLocal

/-! The actual regular matrix and singular window in the monomial basis. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

theorem rising_integral (S : Subring ℚ) (a : ℚ) (ha : a ∈ S) (m : ℕ) :
    PolyInSubring S (rising a m) := by
  unfold rising
  apply polyInSubring_prod
  intro j _
  exact polyInSubring_add polyInSubring_X (polyInSubring_C (S.add_mem ha (natCast_mem S j)))

theorem normalization_integral (n p : ℕ) [Fact p.Prime] (hp : 50*n < p) :
    normalization n ∈ sixGateIntegralRing p := by
  let S := sixGateIntegralRing p
  unfold normalization
  rw [div_eq_mul_inv]
  apply S.mul_mem
  · exact S.mul_mem (natCast_mem S 2) (S.prod_mem (fun b _ => natCast_mem S _))
  · apply sixGateIntegralRing_inv_of_unit
    · exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (25*n))
    · rw [padicValRat.pow, six_factorial_padicValRat_zero (25*n) p Fact.out (by omega), mul_zero]

theorem numerator_integral (n : ℕ) (S : Subring ℚ) :
    PolyInSubring S (numerator n) := by
  unfold numerator
  apply polyInSubring_mul (polyInSubring_add polyInSubring_X (polyInSubring_C (natCast_mem S _)))
  apply polyInSubring_pow
  apply polyInSubring_mul
  · exact rising_integral _ _ S.one_mem _
  · apply rising_integral
    exact S.add_mem (S.mul_mem (natCast_mem S 93) (natCast_mem S n)) (natCast_mem S 2)

private theorem pole_diff_inv_mem (n p a k : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (ha : a ∈ kernelPoleSet n) (hk : k ∈ kernelPoleSet n) (hne : a ≠ k) :
    ((a : ℚ)-k)⁻¹ ∈ sixGateIntegralRing p := by
  have ha' := kernel_pole_address_bounds n a ha
  have hk' := kernel_pole_address_bounds n k hk
  let z : ℤ := (a : ℤ)-k
  have hzne : z ≠ 0 := by dsimp [z]; omega
  have hzabs : z.natAbs < p := by dsimp [z]; omega
  have hzd : ¬ (p : ℤ) ∣ z := by
    intro hd
    have hn : p ∣ z.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hzne) hzabs) hn
  have hzval : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hzd]
    rfl
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hzne
  simpa [z] using sixGateIntegralRing_inv_of_unit p (z : ℚ) hzq hzval

theorem cofactor_integral (n p k : ℕ) [Fact p.Prime] (hk : k ∈ kernelPoleSet n) :
    PolyInSubring (sixGateIntegralRing p) (taylor (-(k : ℚ)) (regularDenominator n k)) := by
  let S := sixGateIntegralRing p
  rw [regularDenominator_eq_erase n k hk]
  apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S k))
  apply polyInSubring_prod
  intro a _
  exact polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C (natCast_mem S a))) _

theorem cofactor_inv_coeff_mem (n p k : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (hk : k ∈ kernelPoleSet n) :
    ((taylor (-(k : ℚ)) (regularDenominator n k)).coeff 0)⁻¹ ∈ sixGateIntegralRing p := by
  rw [regularDenominator_eq_erase n k hk, taylor_coeff_zero, eval_prod, ← Finset.prod_inv_distrib]
  apply (sixGateIntegralRing p).prod_mem
  intro a ha
  simp only [eval_pow,eval_add,eval_X,eval_C,← inv_pow]
  rw [add_comm,← sub_eq_add_neg]
  exact (sixGateIntegralRing p).pow_mem (pole_diff_inv_mem n p a k hp
    (mem_erase.mp ha).2 hk (mem_erase.mp ha).1) _

/-- Coefficients of the original local quotient stay in the local ring when
the divisor has an invertible constant coefficient in that ring. -/
theorem localQuotient_mem {S : Subring ℚ} {A D : ℚ[X]}
    (ha : PolyInSubring S A) (hd : PolyInSubring S D) (hdu : (D.coeff 0)⁻¹ ∈ S) :
    ∀ r, localQuotient A D r ∈ S := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [localQuotient,div_eq_mul_inv]
    refine S.mul_mem (S.sub_mem (ha r) (S.sum_mem ?_)) hdu
    intro i _
    exact S.mul_mem (hd _) (ih i.val i.isLt)

/-- All monomial principal coefficients are integral at each prime p > 50n. -/
theorem monomial_principal_mem (n p k ℓ i j : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (hk : k ∈ kernelPoleSet n) :
    localPrincipal n k ℓ (X^(2*i)) (X^(2*j)) ∈ sixGateIntegralRing p := by
  let S := sixGateIntegralRing p
  unfold localPrincipal
  apply localQuotient_mem
  · apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S k))
    apply polyInSubring_mul
    · exact polyInSubring_mul (polyInSubring_C (normalization_integral n p hp)) (numerator_integral n S)
    · apply polyInSubring_comp
      · exact polyInSubring_mul (polyInSubring_pow polyInSubring_X _) (polyInSubring_pow polyInSubring_X _)
      · exact polyInSubring_add polyInSubring_X (polyInSubring_C (natCast_mem S (center n)))
  · exact cofactor_integral n p k hk
  · exact cofactor_inv_coeff_mem n p k hp hk

def rationalZetaEntry (q : Fin 5 → ℚ) (ℓ : ℕ) : ℚ :=
  ∑ a : Fin 5, if ℓ=3+2*a.val then q a else 0

theorem zetaSymbol_eval_rat (q : Fin 5 → ℚ) (ℓ : ℕ) :
    MvPolynomial.eval q (zetaSymbol ℓ) = rationalZetaEntry q ℓ := by
  simp [zetaSymbol, rationalZetaEntry, apply_ite]

def harmonicSingular (p s m : ℕ) : ℚ :=
  if p ≤ m then 1/(p : ℚ)^s else 0

def regularHigh (n p : ℕ) (q : Fin 5 → ℚ) :
    Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℚ := fun i j =>
  ∑ k ∈ (poleList n).toFinset, ∑ ℓ ∈ Finset.Icc 1 (poleOrder n k),
    ((ℓ+3).choose 4 : ℚ) * localPrincipal n k ℓ (X^(2*i.val)) (X^(2*j.val)) *
      (rationalZetaEntry q ℓ - harmonicRegularPart p (ℓ+4) (k-25*n-1))

def singularHigh (n p : ℕ) :
    Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℚ := fun i j =>
  -(∑ k ∈ (poleList n).toFinset, ∑ ℓ ∈ Finset.Icc 1 (poleOrder n k),
    ((ℓ+3).choose 4 : ℚ) * localPrincipal n k ℓ (X^(2*i.val)) (X^(2*j.val)) *
      harmonicSingular p (ℓ+4) (k-25*n-1))

theorem monomial_high_prime_split (n p : ℕ) (hp : 0 < p) (q : Fin 5 → ℚ) :
    (Hpow n).map (MvPolynomial.eval q) = regularHigh n p q + singularHigh n p := by
  ext i j
  change MvPolynomial.eval q (fiveEntry n (X^(2*i.val)) (X^(2*j.val))) = _
  unfold fiveEntry
  simp only [map_sum,map_mul,MvPolynomial.eval_C,map_sub,zetaSymbol_eval_rat,
    regularHigh,singularHigh,Matrix.add_apply]
  simp_rw [harmonic_eq, harmonicCutoff_split_at_prime p _ _ hp, ← harmonicSingular.eq_1,
    sub_add_eq_sub_sub, mul_sub, Finset.sum_sub_distrib]
  ring

theorem regularHigh_mem (n p : ℕ) [Fact p.Prime] (hp : 50*n < p) (q : Fin 5 → ℚ)
    (hq : ∀ a, q a ∈ sixGateIntegralRing p) (i j : Fin (fiveRank n)) :
    regularHigh n p q i j ∈ sixGateIntegralRing p := by
  let S := sixGateIntegralRing p
  unfold regularHigh
  apply S.sum_mem
  intro k hk
  apply S.sum_mem
  intro ℓ _
  have hk' : k ∈ kernelPoleSet n := by rwa [kernelPoleSet_eq_poleList]
  have hb := (kernel_pole_address_bounds n k hk').2
  apply S.mul_mem (S.mul_mem (natCast_mem S _) (monomial_principal_mem n p k ℓ _ _ hp hk'))
  apply S.sub_mem
  · unfold rationalZetaEntry
    apply S.sum_mem
    intro a _
    split_ifs
    · exact hq a
    · exact S.zero_mem
  · exact harmonicRegularPart_mem _ _ _ (by omega : k-25*n-1 < 2*p)

/-- The singular part has empty harmonic support beyond the endpoint 59n. -/
theorem singularHigh_zero_of_large (n p : ℕ) (hp : 59*n < p) :
    singularHigh n p = 0 := by
  ext i j
  unfold singularHigh
  rw [Matrix.zero_apply]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro ℓ _
  have hk' : k ∈ kernelPoleSet n := by rwa [kernelPoleSet_eq_poleList]
  have hb := (kernel_pole_address_bounds n k hk').2
  simp [harmonicSingular, show ¬ p ≤ k-25*n-1 by omega]

/-- Beyond 59n the evaluated monomial determinant is integral at p. -/
theorem monomial_det_mem_of_large (n p : ℕ) [Fact p.Prime] (hp : 59*n < p)
    (q : Fin 5 → ℚ) (hq : ∀ a, q a ∈ sixGateIntegralRing p) :
    ((Hpow n).map (MvPolynomial.eval q)).det ∈ sixGateIntegralRing p := by
  rw [monomial_high_prime_split n p (Fact.out : p.Prime).pos q,
    singularHigh_zero_of_large n p hp, add_zero, Matrix.det_apply']
  let S := sixGateIntegralRing p
  apply S.sum_mem
  intro σ _
  apply S.mul_mem
  · exact intCast_mem S _
  · apply S.prod_mem
    intro i _
    exact regularHigh_mem n p (by omega) q hq _ _

end OddZetaSix.B40a
