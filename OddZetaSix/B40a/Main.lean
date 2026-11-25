import OddZetaSix.B40a.Analysis.AnalyticRate
import OddZetaSix.B40a.Arithmetic.ArithRate
import OddZetaSix.B40a.Padic.ConcreteGate

namespace OddZetaSix.B40a

/-- At least one of the five indicated values of Mathlib's Riemann zeta
function has irrational real part. -/
theorem exists_irrational_riemannZeta_seven_to_fifteen :
    ∃ s ∈ ({7,9,11,13,15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re) :=
  exists_irrational_riemannZeta_seven_to_fifteen_of_analytic_arithmetic
    determinant_analytic_rate content_arithmetic_exp

end OddZetaSix.B40a
