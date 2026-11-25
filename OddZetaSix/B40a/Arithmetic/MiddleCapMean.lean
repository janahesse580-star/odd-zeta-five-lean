import OddZetaSix.B40a.Arithmetic.MiddleWallOrder

namespace OddZetaSix.B40a.Cert
open MeasureTheory

/-- Within one fixed-wall row, unclipped layer totals and the row penalty
are affine. The rank cap and choosing a row index are both minima. -/
inductive MiddleCapExpr where
  | line (slope intercept : ℝ)
  | add (u v : MiddleCapExpr)
  | minimum (u v : MiddleCapExpr)

namespace MiddleCapExpr

def eval : MiddleCapExpr → ℝ → ℝ
  | .line m c,x => m*x+c
  | .add u v,x => u.eval x+v.eval x
  | .minimum u v,x => min (u.eval x) (v.eval x)

theorem eval_continuous (e : MiddleCapExpr) : Continuous e.eval := by
  induction e with
  | line m c => exact (continuous_const.mul continuous_id).add continuous_const
  | add u v hu hv => exact hu.add hv
  | minimum u v hu hv => exact hu.min hv

/-- Select the active branch at the midpoint, also at ties. This produces a
global affine majorant without locating any crossing of the clipped layers. -/
theorem support_at (e : MiddleCapExpr) (x₀ : ℝ) :
    ∃ m c : ℝ, e.eval x₀=m*x₀+c ∧ ∀ x, e.eval x≤m*x+c := by
  induction e with
  | line m c => exact ⟨m,c,rfl,fun _ => le_rfl⟩
  | add u v hu hv =>
    obtain ⟨m,c,he,hle⟩ := hu
    obtain ⟨s,b,hf,hlt⟩ := hv
    refine ⟨m+s,c+b,?_,?_⟩
    · simp only [eval,he,hf]; ring
    · intro x; simp only [eval,add_mul]; linarith only [hle x,hlt x]
  | minimum u v hu hv =>
    by_cases h : u.eval x₀≤v.eval x₀
    · obtain ⟨m,c,he,hle⟩ := hu
      exact ⟨m,c,(min_eq_left h).trans he,fun x => (min_le_left _ _).trans (hle x)⟩
    · obtain ⟨m,c,he,hle⟩ := hv
      exact ⟨m,c,(min_eq_right (le_of_not_ge h)).trans he,fun x => (min_le_right _ _).trans (hle x)⟩

/-- The rigorous one-midpoint upper rule for a finite capped affine model.
No differentiability or quadrature penalty is required at its kinks. -/
theorem integral_le_midpoint (e : MiddleCapExpr) {a b : ℝ} (hab : a≤b) :
    (∫ x in a..b,e.eval x) ≤ (b-a)*e.eval ((a+b)/2) := by
  obtain ⟨m,c,he,hle⟩ := e.support_at ((a+b)/2)
  have hi : Continuous (fun x : ℝ => m*x+c) := by fun_prop
  calc
    _ ≤ ∫ x in a..b,m*x+c := intervalIntegral.integral_mono_on hab
      (e.eval_continuous.intervalIntegrable a b) (hi.intervalIntegrable a b) (fun x _ => hle x)
    _ = _ := by
      rw [he,intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        intervalIntegrable_const,intervalIntegral.integral_const_mul,integral_id,
        intervalIntegral.integral_const,smul_eq_mul]
      ring

end MiddleCapExpr
end OddZetaSix.B40a.Cert
