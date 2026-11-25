import OddZetaSix.B40a.Identity.Evaluation
import OddZetaSix.B40a.Identity.Basis
import OddZetaSix.B40a.Padic.Subsequence

/-! Assembly after proving the partial-fraction evaluation identity. -/
namespace OddZetaSix.B40a

theorem Hpoly_det_eval_rat_basis (n : ℕ) (q : Fin 5 → ℚ) :
    ((Hpoly n).map (MvPolynomial.eval q)).det =
      basisFactor n * ((Hpow n).map (MvPolynomial.eval q)).det := by
  change ((MvPolynomial.eval q).mapMatrix (Hpoly n)).det = _
  rw [← RingHom.map_det, Hpoly_det_basis_change, map_mul, MvPolynomial.eval_C]
  rw [RingHom.map_det]
  rfl

theorem concrete_valuation_from_reduced_unit (n : ℕ) [Fact (primeIndex n).Prime]
    (q : Fin 5 → ℚ) (u : sixGateIntegralRing (primeIndex n))
    (hu : sixGateReduction (primeIndex n) u ≠ 0)
    (hscaled : (primeIndex n : ℚ)^(240*n)*((Hpow n).map (MvPolynomial.eval q)).det = (u : ℚ)) :
    ((Hpoly n).map (MvPolynomial.eval q)).det ≠ 0 ∧
      padicValRat (primeIndex n) ((Hpoly n).map (MvPolynomial.eval q)).det =
        -269*(n : ℤ)+2 :=
  valuation_from_reduced_unit n u hu hscaled (Hpoly_det_eval_rat_basis n q)

theorem exists_irrational_riemannZeta_seven_to_fifteen_of_gate_and_rates
    (gate : ∀ Q : ℤ, 0 < Q → ∀ N : ℕ, ∃ n ≥ N,
      ∀ q : Fin 5 → ℚ, (∀ k, ∃ z : ℤ, (Q : ℚ)*q k = (z : ℚ)) →
        (primitive n).eval₂ (Int.castRingHom ℚ) q ≠ 0)
    (analytic : ∀ᶠ n : ℕ in Filter.atTop,
      |(fiveFunctional n).det| ≤ Real.exp ((-619/100 : ℝ)*normalizer n))
    (arithmetic : ∀ᶠ n : ℕ in Filter.atTop,
      |(content n : ℝ)|⁻¹ ≤ Real.exp ((61405/10000 : ℝ)*normalizer n)) :
    ∃ s ∈ ({7,9,11,13,15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re) :=
  exists_irrational_riemannZeta_seven_to_fifteen_of_rates Hpoly_det_eval gate analytic arithmetic

end OddZetaSix.B40a
