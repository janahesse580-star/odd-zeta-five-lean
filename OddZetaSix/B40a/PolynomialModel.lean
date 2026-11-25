import OddZetaSix.B40a.Assembly

noncomputable section
open Polynomial
open scoped BigOperators

namespace OddZetaSix.B40a

abbrev FivePolynomial := MvPolynomial (Fin 5) ℚ

def poleList (n : ℕ) : List ℕ := (List.ofFn offsets).flatMap fun d =>
  (List.range ((50-2*d)*n+1)).map fun j => (34+d)*n+1+j

def poleOrder (n k : ℕ) : ℕ := (poleList n).count k

def regularDenominator (n k : ℕ) : ℚ[X] :=
  ((poleList n).filter (· ≠ k) |>.map (fun (t : ℕ) => X+C (t : ℚ))).prod

/-- The Taylor coefficients of A/D at the new origin, with recurrence from A = DQ. -/
def localQuotient (A D : ℚ[X]) (r : ℕ) : ℚ :=
  (A.coeff r - ∑ i : Fin r, D.coeff (r-i.val)*localQuotient A D i.val) / D.coeff 0
termination_by r
decreasing_by exact i.isLt

def localPrincipal (n k ℓ : ℕ) (f g : ℚ[X]) : ℚ :=
  localQuotient
    (taylor (-(k : ℚ)) (C (normalization n) * numerator n *
      (f*g).comp (X+C (center n : ℚ))))
    (taylor (-(k : ℚ)) (regularDenominator n k)) (poleOrder n k-ℓ)

def lowerHarmonic (s m : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 m, 1/(b : ℚ)^s

def zetaSymbol (ℓ : ℕ) : FivePolynomial :=
  ∑ a : Fin 5, if ℓ=3+2*a.val then MvPolynomial.X a else 0

def fiveEntry (n : ℕ) (f g : ℚ[X]) : FivePolynomial :=
  ∑ k ∈ (poleList n).toFinset, ∑ ℓ ∈ Finset.Icc 1 (poleOrder n k),
    MvPolynomial.C ((ℓ+3).choose 4 * localPrincipal n k ℓ f g) *
      (zetaSymbol ℓ - MvPolynomial.C (lowerHarmonic (ℓ+4) (k-25*n-1)))

def Hpoly (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) FivePolynomial :=
  fun i j => fiveEntry n (evenBasis i) (evenBasis j)

def Hpow (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) FivePolynomial :=
  fun i j => fiveEntry n (X^(2*i.val)) (X^(2*j.val))

theorem symbol_degree (ℓ : ℕ) : (zetaSymbol ℓ).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  split_ifs <;> simp

theorem entry_degree (n : ℕ) (f g : ℚ[X]) : (fiveEntry n f g).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ℓ hℓ
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C,zero_add]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (symbol_degree ℓ) (by simp))

theorem Hpoly_degree (n : ℕ) : (Hpoly n).det.totalDegree ≤ fiveRank n := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hs : ((Equiv.Perm.sign σ : ℤ) : FivePolynomial).totalDegree = 0 := by
    change (MvPolynomial.C (Equiv.Perm.sign σ : ℚ)).totalDegree = 0
    exact MvPolynomial.totalDegree_C _
  rw [hs,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i : Fin (fiveRank n), (Hpoly n (σ i) i).totalDegree ≤ ∑ _ : Fin (fiveRank n), 1 :=
      Finset.sum_le_sum (fun i _ => entry_degree n _ _)
    _ = fiveRank n := by simp

/-- Parameter-generic adaptation of the original normalization proof. -/
theorem exists_content_normalization {σ : Type*} (F : MvPolynomial σ ℚ) (hF : F ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ P : MvPolynomial σ ℤ,
      P ≠ 0 ∧ integerPolynomialContent P = 1 ∧
      F = MvPolynomial.C c * P.map (Int.castRingHom ℚ) ∧
      P.totalDegree = F.totalDegree := by
  obtain ⟨D, hD, A, hA⟩ := exists_integer_coefficient_multiple F
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hCD : (MvPolynomial.C (D : ℚ) : MvPolynomial σ ℚ) ≠ 0 := by simpa using hD'
  have hAne : A ≠ 0 := by
    intro hzero
    apply mul_ne_zero hCD hF
    simpa [hzero] using hA.symm
  obtain ⟨P,hAP,hprimitive,hP⟩ := exists_integer_primitive_part A hAne
  let g := integerPolynomialContent A
  have hg : g ≠ 0 := integerPolynomialContent_ne_zero A hAne
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hc : (g : ℚ)/(D : ℚ) ≠ 0 := div_ne_zero hg' hD'
  have hscalar : (D : ℚ)*((g : ℚ)/(D : ℚ)) = g := by field_simp
  have hnorm : F = MvPolynomial.C ((g : ℚ)/(D : ℚ)) * P.map (Int.castRingHom ℚ) := by
    apply mul_left_cancel₀ hCD
    rw [← mul_assoc, ← MvPolynomial.C_mul, hscalar, ← hA, hAP]
    simp only [map_mul, MvPolynomial.map_C]
    rfl
  exact ⟨_,hc,P,hP,hprimitive,hnorm,normalized_integral_totalDegree P F _ hc hnorm⟩

def content (n : ℕ) : ℚ :=
  if h : (Hpoly n).det = 0 then 1 else
    Classical.choose (exists_content_normalization (Hpoly n).det h)

def primitive (n : ℕ) : MvPolynomial (Fin 5) ℤ :=
  if h : (Hpoly n).det = 0 then 0 else
    Classical.choose (Classical.choose_spec (exists_content_normalization (Hpoly n).det h)).2

theorem content_ne_zero (n : ℕ) : content n ≠ 0 := by
  unfold content
  split_ifs with h
  · exact one_ne_zero
  · exact (Classical.choose_spec (exists_content_normalization (Hpoly n).det h)).1

theorem primitive_det_eq (n : ℕ) : (Hpoly n).det =
    MvPolynomial.C (content n) * (primitive n).map (Int.castRingHom ℚ) := by
  unfold content primitive
  split_ifs with h
  · simp [h]
  · exact (Classical.choose_spec
      (Classical.choose_spec (exists_content_normalization (Hpoly n).det h)).2).2.2.1

theorem primitive_degree (n : ℕ) : (primitive n).totalDegree ≤ fiveRank n := by
  rw [normalized_integral_totalDegree _ _ _ (content_ne_zero n) (primitive_det_eq n)]
  exact Hpoly_degree n

theorem primitive_eval_formal (n : ℕ) :
    (content n : ℝ) * (primitive n).eval₂ (Int.castRingHom ℝ) fiveValues =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) fiveValues (Hpoly n).det := by
  have hring : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext fun z => by simp
  rw [primitive_det_eq n, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_map, hring]
  rfl

/-- Assembly with the concrete content and primitive polynomials. The three
rate/gate hypotheses and the analytic partial-fraction identity are explicit. -/
theorem exists_irrational_riemannZeta_seven_to_fifteen_of_rates
    (identity : ∀ n, MvPolynomial.eval₂ (algebraMap ℚ ℝ) fiveValues (Hpoly n).det =
      (fiveFunctional n).det)
    (gate : ∀ Q : ℤ, 0 < Q → ∀ N : ℕ, ∃ n ≥ N,
      ∀ q : Fin 5 → ℚ, (∀ k, ∃ z : ℤ, (Q : ℚ)*q k = (z : ℚ)) →
        (primitive n).eval₂ (Int.castRingHom ℚ) q ≠ 0)
    (analytic : ∀ᶠ n : ℕ in Filter.atTop,
      |(fiveFunctional n).det| ≤ Real.exp ((-619/100 : ℝ)*normalizer n))
    (arithmetic : ∀ᶠ n : ℕ in Filter.atTop,
      |(content n : ℝ)|⁻¹ ≤ Real.exp ((61405/10000 : ℝ)*normalizer n)) :
    ∃ s ∈ ({7,9,11,13,15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re) :=
  exists_irrational_riemannZeta_seven_to_fifteen_of_inputs
    ⟨primitive,content,content_ne_zero,primitive_degree,
      fun n => (primitive_eval_formal n).trans (identity n),gate,analytic,arithmetic⟩

end OddZetaSix.B40a
