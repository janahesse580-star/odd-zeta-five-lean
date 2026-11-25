import OddZetaSix.B40a.Arithmetic.Coarse
import OddZetaSix.B40a.Padic.HighPrimeSplit

/-! The symbolic high-prime split and the exact basis valuation for B40a. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

theorem valProd {ι : Type} {p : ℕ} [Fact p.Prime] (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    padicValRat p (∏ i ∈ s, a i) = ∑ i ∈ s, padicValRat p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hti := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hit, Finset.sum_insert hit,
      padicValRat.mul (ha i (Finset.mem_insert_self i t)) (Finset.prod_ne_zero_iff.mpr hti),
      ih hti]

theorem high_basis_factor_valuation (n p : ℕ) [Fact p.Prime] (hp50 : 50*n < p) :
    padicValRat p (basisFactor n) = -2*((40*n-(p+1)/2 : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  by_cases hn : n=0
  · subst n
    simp [basisFactor]
  have hp2 : 2 < p := by omega
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    have hh : padicValNat p 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
    simpa [hh] using (padicValRat_of_nat (p := p) 2).symm
  have hterm (i : ℕ) :
      padicValRat p (((2 : ℚ) / ((2*i).factorial : ℚ)) ^ 2) =
        -2 * (padicValNat p (2*i).factorial : ℤ) := by
    rw [padicValRat.pow,padicValRat.div (by norm_num) (by positivity),h2,← padicValRat_of_nat]
    ring
  have hsum : (∑ i ∈ Ico 1 (40*n), padicValNat p (2*i).factorial) = 40*n-(p+1)/2 := by
    let c := (p+1)/2
    have hcount : 1 ≤ c := by dsimp [c]; omega
    calc
      _ = ∑ i ∈ Ico 1 (40*n), if c ≤ i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib := (mem_Ico.mp hi).2
        rw [factorial_val_lt_twice _ _ (by omega)]
        simp only [show p ≤ 2*i ↔ c ≤ i by dsimp [c]; omega]
      _ = ∑ _i ∈ (Ico 1 (40*n)).filter (fun i => c ≤ i), (1 : ℕ) := by
        rw [Finset.sum_filter]
      _ = _ := by
        have he : (Ico 1 (40*n)).filter (fun i => c ≤ i) = Ico c (40*n) := by
          ext i
          simp only [mem_filter,mem_Ico]
          omega
        rw [he]
        simp [c]
  unfold basisFactor
  rw [valProd _ _ (fun i _ => by positivity)]
  simp_rw [hterm]
  rw [← Finset.mul_sum,← Nat.cast_sum,hsum]

def regularHighFormal (n p : ℕ) (i j : Fin (fiveRank n)) : FivePolynomial :=
  ∑ k ∈ (poleList n).toFinset, ∑ ℓ ∈ Icc 1 (poleOrder n k),
    MvPolynomial.C (((ℓ+3).choose 4 : ℚ)*localPrincipal n k ℓ (X^(2*i.val)) (X^(2*j.val))) *
      (zetaSymbol ℓ - MvPolynomial.C (harmonicRegularPart p (ℓ+4) (k-25*n-1)))

theorem Hpow_formal_high_split (n p : ℕ) (hp : 0<p) (i j : Fin (fiveRank n)) :
    Hpow n i j = regularHighFormal n p i j + MvPolynomial.C (singularHigh n p i j) := by
  simp only [Hpow,fiveEntry,regularHighFormal,singularHigh,map_neg,map_sum,map_mul]
  simp_rw [harmonic_eq,harmonicCutoff_split_at_prime p _ _ hp,← harmonicSingular.eq_1,
    map_add,sub_add_eq_sub_sub,mul_sub,Finset.sum_sub_distrib]
  ring

theorem regularHighFormal_integral (n p : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (i j : Fin (fiveRank n)) : FormalValAtLeast p 0 (regularHighFormal n p i j) := by
  unfold regularHighFormal
  apply formalValAtLeast_sum
  intro k hk
  apply formalValAtLeast_sum
  intro ℓ _
  have hk' : k ∈ kernelPoleSet n := by rwa [kernelPoleSet_eq_poleList]
  have hb := (kernel_pole_address_bounds n k hk').2
  refine formalValAtLeast_mono (@formalValAtLeast_C_mul p _ 0 0 _ _ ?_ ?_) (by omega)
  · have hmem := monomial_principal_mem n p k ℓ i.val j.val hp hk'
    exact valAtLeast_mul (valAtLeast_natCast p _)
      (Or.inr ((sixGateIntegralRing_mem_iff p _).mp hmem))
  · apply formalValAtLeast_sub
    · unfold zetaSymbol
      apply formalValAtLeast_sum
      intro a _
      split_ifs
      · exact formalValAtLeast_X p a
      · exact formalValAtLeast_zero p 0
    · apply formalValAtLeast_C
      have hmem := harmonicRegularPart_mem p (ℓ+4) (k-25*n-1) (by omega)
      exact Or.inr ((sixGateIntegralRing_mem_iff p _).mp hmem)

theorem Hpow_formal_integral_of_large (n p : ℕ) [Fact p.Prime] (hp : 59*n < p)
    (i j : Fin (fiveRank n)) : FormalValAtLeast p 0 (Hpow n i j) := by
  rw [Hpow_formal_high_split n p (Fact.out : p.Prime).pos,singularHigh_zero_of_large n p hp,
    Matrix.zero_apply,map_zero,add_zero]
  exact regularHighFormal_integral n p (by omega) i j

/-- The entire regular band beyond the harmonic-support endpoint, with the
even factorial change of basis included. -/
theorem content_high_regular_bound (n p : ℕ) [Fact p.Prime] (hp : 59*n < p) :
    -padicValRat p (content n) ≤ 2*((40*n-(p+1)/2 : ℕ) : ℤ) := by
  let v : ℤ := -2*((40*n-(p+1)/2 : ℕ) : ℤ)
  have hv : ValAtLeast p v (basisFactor n) := by
    right
    rw [high_basis_factor_valuation n p (by omega)]
  have hd := formalValAtLeast_det_uniform (Hpow n) 0 (Hpow_formal_integral_of_large n p hp)
  have hd' : FormalValAtLeast p 0 (Hpow n).det := by simpa using hd
  have hc : FormalValAtLeast p v (Hpoly n).det := by
    rw [Hpoly_det_basis_change]
    simpa using formalValAtLeast_C_mul hv hd'
  have hv0 : v ≤ 0 := by
    dsimp [v]
    exact mul_nonpos_of_nonpos_of_nonneg (by decide) (Int.natCast_nonneg _)
  have h := content_padicValRat_ge_of_formal_nonpos n p v hv0 hc
  dsimp [v] at h
  linarith

end OddZetaSix.B40a
