import OddZetaSix.B40a.Identity.Basis
import OddZetaSix.SixSmallPrimes

/-! Coefficientwise valuation on the concrete five-variable determinant. The general valuation argument is adapted from the MIT-licensed upstream SixSmallPrimes module. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators
/-- Coefficientwise zero-safe `p`-adic valuation lower bound on `FivePolynomial`. -/
def FormalValAtLeast (p : ℕ) (a : ℤ) (F : FivePolynomial) : Prop :=
  ∀ m : Fin 5 →₀ ℕ, ValAtLeast p a (F.coeff m)

theorem formalValAtLeast_zero (p : ℕ) (a : ℤ) : FormalValAtLeast p a 0 := fun m => by
  simp [valAtLeast_zero]

theorem formalValAtLeast_mono {p : ℕ} {a b : ℤ} {F : FivePolynomial}
    (h : FormalValAtLeast p a F) (hab : b ≤ a) : FormalValAtLeast p b F :=
  fun m => valAtLeast_mono (h m) hab

theorem formalValAtLeast_C {p : ℕ} {a : ℤ} {c : ℚ} (hc : ValAtLeast p a c) :
    FormalValAtLeast p a (MvPolynomial.C c) := by
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · exact valAtLeast_zero p a

theorem formalValAtLeast_one (p : ℕ) [Fact p.Prime] : FormalValAtLeast p 0 1 := by
  simpa using formalValAtLeast_C (valAtLeast_one p)

theorem formalValAtLeast_X (p : ℕ) [Fact p.Prime] (s : Fin 5) :
    FormalValAtLeast p 0 (MvPolynomial.X s) := by
  intro m
  rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
  split_ifs
  · exact valAtLeast_one p
  · exact valAtLeast_zero p 0

theorem formalValAtLeast_neg {p : ℕ} {a : ℤ} {F : FivePolynomial}
    (h : FormalValAtLeast p a F) : FormalValAtLeast p a (-F) := by
  intro m; rw [MvPolynomial.coeff_neg]; exact valAtLeast_neg (h m)

theorem formalValAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : FivePolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p a G) :
    FormalValAtLeast p a (F + G) := by
  intro m
  have h : (F + G).coeff m = F.coeff m + G.coeff m := by simp
  rw [h]
  exact valAtLeast_add (hF m) (hG m)

theorem formalValAtLeast_sub {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : FivePolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p a G) :
    FormalValAtLeast p a (F - G) := by
  simpa only [sub_eq_add_neg] using formalValAtLeast_add hF (formalValAtLeast_neg hG)

theorem formalValAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {F G : FivePolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p b G) :
    FormalValAtLeast p (a + b) (F * G) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  apply valAtLeast_sum
  intro x _
  exact valAtLeast_mul (hF x.1) (hG x.2)

theorem formalValAtLeast_C_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {c : ℚ} {F : FivePolynomial}
    (hc : ValAtLeast p a c) (hF : FormalValAtLeast p b F) :
    FormalValAtLeast p (a + b) (MvPolynomial.C c * F) :=
  formalValAtLeast_mul (formalValAtLeast_C hc) hF

theorem formalValAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → FivePolynomial) (a : ℤ) (hf : ∀ i ∈ s, FormalValAtLeast p a (f i)) :
    FormalValAtLeast p a (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact valAtLeast_sum s (fun i => (f i).coeff m) a (fun i hi => hf i hi m)

theorem formalValAtLeast_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → FivePolynomial) (a : ι → ℤ) (hf : ∀ i ∈ s, FormalValAtLeast p (a i) (f i)) :
    FormalValAtLeast p (∑ i ∈ s, a i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using formalValAtLeast_one p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact formalValAtLeast_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem formalValAtLeast_det_uniform {p h : ℕ} [Fact p.Prime]
    (M : Matrix (Fin h) (Fin h) FivePolynomial) (b : ℤ)
    (hM : ∀ i j : Fin h, FormalValAtLeast p b (M i j)) :
    FormalValAtLeast p ((h : ℤ) * b) M.det := by
  rw [Matrix.det_apply]
  apply formalValAtLeast_sum
  intro σ _
  have hprod := formalValAtLeast_prod (Finset.univ : Finset (Fin h))
    (fun i => M (σ i) i) (fun _ => b) (fun i _ => hM (σ i) i)
  have hsum : (∑ _i : Fin h, b) = (h : ℤ) * b := by
    simp [Finset.sum_const]
  rw [hsum] at hprod
  intro m
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod m
  · rw [hs, Units.neg_smul, one_smul, MvPolynomial.coeff_neg]; exact valAtLeast_neg (hprod m)


theorem primitive_content_eq_one (n : ℕ) (h : (Hpoly n).det ≠ 0) :
    integerPolynomialContent (primitive n) = 1 := by
  unfold primitive
  rw [dite_eq_right h]
  exact (Classical.choose_spec
    (Classical.choose_spec (exists_content_normalization (Hpoly n).det h)).2).2.1

/-- Exact Gauss valuation identity: when `(Hpoly n).det ≠ 0`, any coefficientwise floor `L`
on `(Hpoly n).det` is a lower bound on `padicValRat p (content n)`. -/
theorem content_padicValRat_ge_of_formal (n p : ℕ) [Fact p.Prime] (L : ℤ)
    (hL : FormalValAtLeast p L (Hpoly n).det)
    (hdet : (Hpoly n).det ≠ 0) :
    L ≤ padicValRat p (content n) := by
  have hp : p.Prime := Fact.out
  have hprim := primitive_content_eq_one n hdet
  obtain ⟨m, hm, hnd⟩ := exists_primitive_coeff_not_dvd (primitive n) hprim p hp
  have hPne : ((primitive n).coeff m : ℚ) ≠ 0 := by
    intro h0
    have hZ : (primitive n).coeff m = 0 := by exact_mod_cast h0
    exact MvPolynomial.mem_support_iff.mp hm hZ
  have hPval : padicValRat p ((primitive n).coeff m : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hnd
  have hcoeff : ((Hpoly n).det).coeff m =
      content n * ((primitive n).coeff m : ℚ) := by
    rw [primitive_det_eq n, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
    rfl
  have hne : ((Hpoly n).det).coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (content_ne_zero n) hPne
  have hval := valAtLeast_of_ne_zero (hL m) hne
  rw [hcoeff, padicValRat.mul (content_ne_zero n) hPne, hPval, add_zero] at hval
  exact hval

/-- Unconditional version when `L ≤ 0` (also handles `(Hpoly n).det = 0`, where
`content n = 1` has valuation `0 ≥ L`). -/
theorem content_padicValRat_ge_of_formal_nonpos (n p : ℕ) [Fact p.Prime] (L : ℤ)
    (hL0 : L ≤ 0) (hL : FormalValAtLeast p L (Hpoly n).det) :
    L ≤ padicValRat p (content n) := by
  by_cases hdet : (Hpoly n).det = 0
  · unfold content
    simp [hdet, hL0]
  · exact content_padicValRat_ge_of_formal n p L hL hdet


end OddZetaSix.B40a
