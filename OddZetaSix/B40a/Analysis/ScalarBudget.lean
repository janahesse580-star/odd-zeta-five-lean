import OddZetaSix.B40a.Analysis.KernelPhase
import OddZetaSix.B40a.Analysis.Subexponential
noncomputable section
namespace OddZetaSix.B40a.Cert
open Filter Real
open scoped Topology

theorem absorb_scalar_budget (p κ c δ : ℝ) (hκ : 0<κ) (hδ : 0<δ) :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ n : ℕ in atTop,
      192*κ*(scaleN n)^2*Real.exp (scaleN n*p+blockError (scaleN n) η+c) ≤
        Real.exp (scaleN n*(p+δ)) := by
  let η := δ/(20*Real.pi)
  refine ⟨η,div_pos hδ (mul_pos (by norm_num) Real.pi_pos),?_⟩
  let A := Real.log (192*κ)+40/η+108+c
  have L := (const_log_over_scale A 14).eventually_lt_const (show 0<δ/2 by linarith)
  filter_upwards [L,eventually_gt_atTop (0:ℕ)] with n hnL hn
  have D : 0<scaleN n := by unfold scaleN; positivity
  rw [←Real.log_le_iff_le_exp (by positivity),Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp,Real.log_mul (by positivity) (pow_ne_zero _ D.ne'),Real.log_pow]
  have B := (div_lt_iff₀ D).mp hnL
  have H : 10*Real.pi*η=δ/2 := by dsimp [η]; field_simp [Real.pi_ne_zero]; ring
  unfold A at B; unfold blockError
  norm_num only [Nat.cast_ofNat]
  nlinarith only [B,congrArg (fun x : ℝ=>scaleN n*x) H]
end OddZetaSix.B40a.Cert
