import OddZetaSix.B40a.Padic.Hermite
import OddZetaSix.SixGateLocal

namespace OddZetaSix.B40a

/-- Applying reduction to the scaled monomial determinant first proves that it
is a p-adic unit. The valuation transfer then yields the B40a exponent. -/
theorem valuation_from_reduced_unit (n : ℕ) [Fact (primeIndex n).Prime]
    {dPow dEven : ℚ} (u : sixGateIntegralRing (primeIndex n))
    (hu : sixGateReduction (primeIndex n) u ≠ 0)
    (hscaled : (primeIndex n : ℚ)^(240*n)*dPow = (u : ℚ))
    (hbasis : dEven = basisFactor n*dPow) :
    dEven ≠ 0 ∧ padicValRat (primeIndex n) dEven = -269*(n : ℤ)+2 := by
  have hp : (primeIndex n).Prime := Fact.out
  obtain ⟨hu0,hv⟩ := (sixGateReduction_ne_zero_iff _ u).mp hu
  have hdp : dPow ≠ 0 := by
    intro hn
    apply hu0
    simpa [hn] using hscaled.symm
  have hppow : (primeIndex n : ℚ)^(240*n) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have e := congrArg (padicValRat (primeIndex n)) hscaled
  rw [padicValRat.mul hppow hdp, padicValRat.pow, padicValRat.self hp.one_lt, hv] at e
  have hlocal : padicValRat (primeIndex n) dPow = -240*(n : ℤ) := by
    push_cast at e
    linarith
  exact det_valuation_after_basis_change hp hdp hlocal hbasis

end OddZetaSix.B40a
