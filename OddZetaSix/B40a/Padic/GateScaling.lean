import OddZetaSix.B40a.Padic.LocalBlock
import OddZetaSix.B40a.Stage2Assembly

/-! Determinants of the concrete jet scalings and their effect on the rational matrix. -/
noncomputable section
namespace OddZetaSix.B40a

def jetScale (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℚ :=
  Matrix.diagonal fun j => (primeIndex n : ℚ) ^ (5-((jetIndex n).symm j).2.val)

theorem jetScale_det (n : ℕ) :
    (jetScale n).det = (primeIndex n : ℚ)^(120*n) := by
  rw [jetScale,Matrix.det_diagonal,Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : (∑ j : Fin (fiveRank n), (5-((jetIndex n).symm j).2.val)) =
      ∑ p : Fin (8*n) × Fin 5, (5-p.2.val) :=
    Fintype.sum_equiv (jetIndex n).symm _ _ (fun _ => rfl)
  rw [hsum,Fintype.sum_prod_type]
  have hinner : (∑ a : Fin 5, (5-a.val)) = 15 := by decide
  simp only [hinner,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

def inverseMonomialJets (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℚ :=
  (monomialJets (K := ℚ) n).det⁻¹ • (monomialJets (K := ℚ) n).adjugate

theorem inverseMonomialJets_mul (n : ℕ) [Fact (primeIndex n).Prime] :
    inverseMonomialJets n * monomialJets n = 1 := by
  have h := (monomialJets_det_unit n).1
  rw [inverseMonomialJets,Matrix.smul_mul,Matrix.adjugate_mul,smul_smul,
    inv_mul_cancel₀ h,one_smul]

theorem inverseMonomialJets_det_unit (n : ℕ) [Fact (primeIndex n).Prime] :
    (inverseMonomialJets n).det ≠ 0 ∧
      padicValRat (primeIndex n) (inverseMonomialJets n).det = 0 := by
  have hg : (inverseMonomialJets n).det * (monomialJets (K := ℚ) n).det = 1 := by
    rw [← Matrix.det_mul,inverseMonomialJets_mul n,Matrix.det_one]
  have hf := left_ne_zero_of_mul_eq_one hg
  have hv := monomialJets_det_unit n
  have h := congrArg (padicValRat (primeIndex n)) hg
  rw [padicValRat.mul hf hv.1,hv.2,add_zero,padicValRat.one] at h
  exact ⟨hf,h⟩

def scaledWindowMatrix (n : ℕ) (q : Fin 5 → ℚ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℚ :=
  jetScale n * inverseMonomialJets n * (Hpow n).map (MvPolynomial.eval q) *
    (inverseMonomialJets n).transpose * jetScale n

/-- A unit reduced determinant of the actual scaled matrix yields the exact
valuation of the even-basis determinant. Producing that unit is separate. -/
theorem concrete_valuation_from_scaled_window (n : ℕ) [Fact (primeIndex n).Prime]
    (q : Fin 5 → ℚ) (hne : (scaledWindowMatrix n q).det ≠ 0)
    (hu : padicValRat (primeIndex n) (scaledWindowMatrix n q).det = 0) :
    ((Hpoly n).map (MvPolynomial.eval q)).det ≠ 0 ∧
      padicValRat (primeIndex n) ((Hpoly n).map (MvPolynomial.eval q)).det = -269*(n : ℤ)+2 := by
  let p := primeIndex n
  let D := ((Hpow n).map (MvPolynomial.eval q)).det
  let W := (inverseMonomialJets n).det
  have hdet : (scaledWindowMatrix n q).det = (p : ℚ)^(240*n)*W^2*D := by
    rw [scaledWindowMatrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,
      Matrix.det_transpose,jetScale_det,show 240*n = 120*n+120*n by omega,pow_add]
    ring
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hD : D ≠ 0 := by
    intro hD
    exact hne (by rw [hdet,hD,mul_zero])
  have hW := inverseMonomialJets_det_unit n
  have hv := hu
  rw [hdet,padicValRat.mul (mul_ne_zero (pow_ne_zero _ hpne) (pow_ne_zero _ hW.1)) hD,
    padicValRat.mul (pow_ne_zero _ hpne) (pow_ne_zero _ hW.1),
    padicValRat.pow, padicValRat.pow, hW.2, padicValRat.self hp.one_lt] at hv
  have hfinal : padicValRat p D = -240*(n : ℤ) := by push_cast at hv; linarith
  exact det_valuation_after_basis_change hp hD hfinal (Hpoly_det_eval_rat_basis n q)

end OddZetaSix.B40a
