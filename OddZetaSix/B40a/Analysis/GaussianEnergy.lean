import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Basic

/-! Finite Gaussian energy positivity, used in logarithmic energy comparison. -/
noncomputable section
namespace OddZetaSix.B40a
open Matrix Finset
open scoped BigOperators

theorem exp_product_sum_nonneg {ι : Type*} [Fintype ι]
    (x a : ι → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ ∑ i, ∑ j, a i * a j * Real.exp (s*x i*x j) := by
  classical
  have he (i j : ι) : HasSum (fun k : ℕ => a i*a j*((s*x i*x j)^k/(k.factorial : ℝ)))
      (a i*a j*Real.exp (s*x i*x j)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (s*x i*x j)).mul_left (a i*a j)
  have ht : HasSum (fun k : ℕ => ∑ i, ∑ j, a i*a j*((s*x i*x j)^k/(k.factorial : ℝ)))
      (∑ i, ∑ j, a i*a j*Real.exp (s*x i*x j)) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => he i j))
  rw [← ht.tsum_eq]
  apply tsum_nonneg
  intro k
  have eqn : (∑ i, ∑ j, a i*a j*((s*x i*x j)^k/(k.factorial : ℝ))) =
      (s^k/(k.factorial : ℝ))*(∑ i, a i*(x i)^k)^2 := by
    rw [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_pow]
    ring
  rw [eqn]
  positivity

private theorem exp_product_posSemidef {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    (Matrix.of fun i j => Real.exp (s*x i*x j)).PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [conjTranspose_apply,of_apply,star_trivial]
    congr 1
    ring
  · intro a
    simpa only [dotProduct,mulVec,of_apply,Pi.star_apply,star_trivial,Finset.mul_sum,
      mul_assoc,mul_comm (Real.exp _) (_ : ℝ)] using exp_product_sum_nonneg x a s hs

private theorem norm_sub_sq (x y : ℂ) :
    ‖x-y‖^2 = ‖x‖^2+‖y‖^2-2*(x.re*y.re+x.im*y.im) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

theorem gaussian_energy_nonneg {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (a : ι → ℝ) (s : ℝ) (hs : 0≤s) :
    0 ≤ ∑ i, ∑ j, a i*a j*Real.exp (-s*‖z i-z j‖^2) := by
  let w := fun i => a i*Real.exp (-s*‖z i‖^2)
  have h := ((exp_product_posSemidef (fun i => (z i).re) (2*s) (by positivity)).hadamard
    (exp_product_posSemidef (fun i => (z i).im) (2*s) (by positivity))).dotProduct_mulVec_nonneg w
  simp only [dotProduct,mulVec,hadamard_apply,of_apply,Pi.star_apply,star_trivial,Finset.mul_sum] at h
  change (0 : ℝ) ≤ ∑ i, ∑ j,
    w i * (Real.exp (2*s*(z i).re*(z j).re)*Real.exp (2*s*(z i).im*(z j).im)*w j) at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold w
  rw [norm_sub_sq]
  rw [show -s*(‖z i‖^2+‖z j‖^2-2*((z i).re*(z j).re+(z i).im*(z j).im)) =
    (-s*‖z i‖^2)+(-s*‖z j‖^2)+(2*s*(z i).re*(z j).re)+(2*s*(z i).im*(z j).im) by ring]
  simp only [Real.exp_add]
  ring

end OddZetaSix.B40a
