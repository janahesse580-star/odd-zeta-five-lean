import OddZetaSix.B40a.PolynomialModel
import OddZetaSix.B40a.Padic.Hermite
import Mathlib.LinearAlgebra.Matrix.Block

/-! Congruence of the actual factorial and monomial moment matrices. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

theorem localQuotient_add (A B D : ℚ[X]) (r : ℕ) :
    localQuotient (A+B) D r = localQuotient A D r + localQuotient B D r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [localQuotient.eq_def (A+B) D r, localQuotient.eq_def A D r, localQuotient.eq_def B D r,coeff_add]
    simp_rw [show ∀ i : Fin r, localQuotient (A+B) D i.val =
      localQuotient A D i.val + localQuotient B D i.val from fun i => ih i.val i.isLt,
      mul_add,Finset.sum_add_distrib]
    ring

theorem localQuotient_C_mul (A D : ℚ[X]) (c : ℚ) (r : ℕ) :
    localQuotient (C c * A) D r = c * localQuotient A D r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [localQuotient.eq_def (C c*A) D r,localQuotient.eq_def A D r,coeff_C_mul]
    simp_rw [show ∀ i : Fin r, localQuotient (C c*A) D i.val =
      c * localQuotient A D i.val from fun i => ih i.val i.isLt]
    have hh : (∑ i : Fin r, D.coeff (r-i.val) * (c*localQuotient A D i.val)) =
        c * ∑ i : Fin r, D.coeff (r-i.val) * localQuotient A D i.val := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [hh]
    ring

def momentMap (n : ℕ) : ℚ[X] →ₗ[ℚ] FivePolynomial where
  toFun f := fiveEntry n f 1
  map_add' f g := by
    unfold fiveEntry localPrincipal
    simp only [mul_one,add_comp,mul_add,map_add,localQuotient_add,map_add,add_mul,
      Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply, Polynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
    unfold fiveEntry localPrincipal
    simp only [mul_one,mul_comp,C_comp]
    have move :
        C (normalization n) * numerator n * (C c * f.comp (X + C (center n : ℚ))) =
          C c * (C (normalization n) * numerator n * f.comp (X + C (center n : ℚ))) := by ring
    simp only [move, taylor_mul,taylor_C,localQuotient_C_mul, map_mul, Finset.mul_sum, mul_sub]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    ring

theorem momentMap_mul (n : ℕ) (f g : ℚ[X]) :
    momentMap n (f*g) = fiveEntry n f g := by
  change fiveEntry n (f*g) 1 = _
  simp only [fiveEntry,localPrincipal,mul_one]

def squareScaling (i : ℕ) : ℚ :=
  if i=0 then 1 else 2 / ((2*i).factorial : ℚ)

def inSquareBasis (i : ℕ) : ℚ[X] := C (squareScaling i) * gateMonicBasis ℚ i

theorem squareScaling_ne_zero (i : ℕ) : squareScaling i ≠ 0 := by
  unfold squareScaling
  split_ifs <;> positivity

theorem inSquareBasis_comp (i : ℕ) : (inSquareBasis i).comp (X^2) = evenBasis i := by
  cases i with
  | zero => simp [inSquareBasis,squareScaling,gateMonicBasis]
  | succ i =>
    simp only [inSquareBasis,squareScaling,Nat.succ_ne_zero,ite_false,gateMonicBasis,
      evenBasis_succ,evenBasisProduct,mul_comp,C_comp,Polynomial.prod_comp,X_comp,sub_comp]

theorem inSquareBasis_degree (i : ℕ) : (inSquareBasis i).natDegree = i := by
  rw [inSquareBasis,natDegree_C_mul (squareScaling_ne_zero _),gateMonicBasis_natDegree]

theorem inSquareBasis_diag_coeff (i : ℕ) : (inSquareBasis i).coeff i = squareScaling i := by
  have h := (gateMonicBasis_monic ℚ i).coeff_natDegree
  rw [gateMonicBasis_natDegree] at h
  rw [inSquareBasis,coeff_C_mul,h,mul_one]

theorem evenBasis_expand (n : ℕ) (i : Fin (fiveRank n)) :
    evenBasis i = ∑ j : Fin (fiveRank n), (inSquareBasis i).coeff j • (X:ℚ[X])^(2*j.val) := by
  have hh := (inSquareBasis i).as_sum_range_C_mul_X_pow'
    (show (inSquareBasis i).natDegree < fiveRank n by rw [inSquareBasis_degree]; exact i.isLt)
  have hc := congrArg (fun p : ℚ[X] => p.comp (X^2)) hh
  simpa only [inSquareBasis_comp,Polynomial.sum_comp,mul_comp,C_comp,pow_comp,X_comp,
    ← pow_mul,← Fin.sum_univ_eq_sum_range,Polynomial.smul_eq_C_mul] using hc

def changeMatrix (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) FivePolynomial :=
  fun i j => MvPolynomial.C ((inSquareBasis i).coeff j)

theorem Hpoly_congruence (n : ℕ) :
    Hpoly n = changeMatrix n * Hpow n * (changeMatrix n).transpose := by
  apply Matrix.ext
  intro i j
  simp only [Hpoly,Hpow,changeMatrix,Matrix.mul_apply,Matrix.transpose_apply]
  rw [← momentMap_mul, evenBasis_expand n i, evenBasis_expand n j,
    Finset.sum_mul, map_sum]
  simp only [Finset.mul_sum,map_sum,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, momentMap_mul,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  ring

theorem changeMatrix_det (n : ℕ) :
    (changeMatrix n).det = MvPolynomial.C (∏ i : Fin (fiveRank n), squareScaling i) := by
  have h : (changeMatrix n).IsLowerTriangular := by
    intro i j hij
    unfold changeMatrix
    rw [coeff_eq_zero_of_natDegree_lt, map_zero]
    rwa [inSquareBasis_degree]
  rw [Matrix.det_of_isLowerTriangular _ h, map_prod]
  apply prod_congr rfl
  intro i _
  rw [changeMatrix, inSquareBasis_diag_coeff]

theorem basisFactor_eq_square (n : ℕ) :
    (∏ i : Fin (fiveRank n), squareScaling i)^2 = basisFactor n := by
  rw [Fin.prod_univ_eq_prod_range]
  unfold basisFactor
  by_cases hn : n=0
  · subst n
    simp [fiveRank]
  rw [Finset.prod_range_eq_mul_Ico _ (by unfold fiveRank; omega),squareScaling]
  simp only [ite_true,one_mul,Finset.prod_pow, fiveRank]
  congr 1
  apply prod_congr rfl
  intro i hi
  unfold squareScaling
  have him := (mem_Ico.mp hi).1
  simp [show i ≠ 0 by omega]

/-- Determinant change of basis for the concrete B40a matrices, before evaluation. -/
theorem Hpoly_det_basis_change (n : ℕ) :
    (Hpoly n).det = MvPolynomial.C (basisFactor n) * (Hpow n).det := by
  rw [Hpoly_congruence, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    changeMatrix_det, ← basisFactor_eq_square, map_pow]
  ring

end OddZetaSix.B40a
