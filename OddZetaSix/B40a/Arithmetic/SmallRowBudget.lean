import OddZetaSix.B40a.Arithmetic.SmallRowEstimate
import OddZetaSix.B40a.Arithmetic.SmallAffineAudit

namespace OddZetaSix.B40a.Cert
open Finset MeasureTheory PeriodAffine
theorem smallRow_budget (r : ArithRow) (hr : r ∈ smallRows) (N : ℕ) :
    (∑ k ∈ Ico (periodStart r.left) N,
      ∫ P in 1/((k:ℝ)+r.right)..1/((k:ℝ)+r.left),smallTileWeight r k P) ≤
        2000*(rowValue true r:ℝ) :=
  smallRow_budget_checked r hr (List.all_eq_true.mp smallRows_affine_check r hr) N

end OddZetaSix.B40a.Cert
