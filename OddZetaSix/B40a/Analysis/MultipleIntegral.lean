import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Vandermonde

/-! Andréief's determinant identity over a sigma-finite measure. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset MeasureTheory Matrix
open scoped BigOperators

def sampleMatrix {d : ℕ} {X : Type*}
    (f : Fin d → X → ℂ) (x : Fin d → X) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => f i (x j)

theorem det_moment_integral {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (f g : Fin d → X → ℂ)
    (h : ∀ i j, Integrable (fun x => f i x*g j x) μ) :
    (∫ x : Fin d → X, (sampleMatrix f x).det*(sampleMatrix g x).det
      ∂Measure.pi (fun _ => μ)) =
      (d.factorial : ℂ) * (Matrix.of (fun i j => ∫ x, f i x*g j x ∂μ)).det := by
  classical
  let prodMeasure := Measure.pi (fun _ : Fin d => μ)
  let A : Matrix (Fin d) (Fin d) ℂ := fun i j => ∫ x, f i x*g j x ∂μ
  let P := fun (τ σ : Equiv.Perm (Fin d)) (x : Fin d → X) =>
    ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i : Fin d, f (σ i) (x i)*g (τ i) (x i)))
  have hP (τ σ) : Integrable (P τ σ) prodMeasure := by
    exact ((Integrable.fintype_prod (fun i : Fin d => h (σ i) (τ i))).const_mul _).const_mul _
  have hexpand (x : Fin d → X) :
      (sampleMatrix f x).det*(sampleMatrix g x).det =
        ∑ τ : Equiv.Perm (Fin d), ∑ σ : Equiv.Perm (Fin d), P τ σ x := by
    rw [Matrix.det_apply',Matrix.det_apply',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    unfold P sampleMatrix
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun τ _ => integrable_finsetSum _ (fun σ _ => hP τ σ))]
  have hiter (τ : Equiv.Perm (Fin d)) :
      (∫ x, ∑ σ : Equiv.Perm (Fin d), P τ σ x ∂prodMeasure) =
        ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin d, A (σ i) (τ i)) := by
    rw [integral_finsetSum _ (fun σ _ => hP τ σ)]
    apply Finset.sum_congr rfl
    intro σ _
    unfold P
    rw [integral_const_mul,integral_const_mul]
    congr 2
    exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => μ)
      (fun i x => f (σ i) x*g (τ i) x)
  simp_rw [hiter]
  change _ = (d.factorial : ℂ)*A.det
  have hs (τ : Equiv.Perm (Fin d)) :
      (∑ σ : Equiv.Perm (Fin d), (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin d, A (σ i) (τ i))) = (A.submatrix id τ).det := by
    rw [Matrix.det_apply']
    rfl
  have he (τ : Equiv.Perm (Fin d)) :
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * (A.submatrix id τ).det = A.det := by
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hτ | hτ <;> simp [hτ]
  simp_rw [← Finset.mul_sum,hs,he]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]

def powerMoment {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w ρ : X → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∫ x, w x^(i.val+j.val)*ρ x ∂μ

/-- Exact squared Vandermonde formula for the power moments of a complex weight. -/
theorem det_powerMoment_integral {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (w ρ : X → ℂ)
    (h : ∀ i j : Fin d, Integrable (fun x => w x^(i.val+j.val)*ρ x) μ) :
    (d.factorial : ℂ)*(powerMoment μ w ρ : Matrix (Fin d) (Fin d) ℂ).det =
      ∫ x : Fin d → X,
        (∏ j : Fin d, ρ (x j)) *
          ((vandermonde (fun j : Fin d => w (x j))).det)^2 ∂Measure.pi (fun _ => μ) := by
  let f := fun (i : Fin d) x => w x^i.val
  let g := fun (i : Fin d) x => w x^i.val*ρ x
  have hf : ∀ i j, Integrable (fun x => f i x*g j x) μ := by
    intro i j
    simpa [f,g,pow_add,mul_assoc] using h i j
  have he : (Matrix.of (fun (i j : Fin d) => ∫ x, f i x*g j x ∂μ)) = powerMoment μ w ρ := by
    ext i j
    simp [powerMoment,f,g,pow_add,mul_assoc]
  rw [← he, ← det_moment_integral μ f g hf]
  apply integral_congr_ae
  filter_upwards with x
  let V := vandermonde (fun j : Fin d => w (x j))
  have hF : sampleMatrix f x = V.transpose := rfl
  have hG : sampleMatrix g x = V.transpose * diagonal (fun j => ρ (x j)) := by
    ext i j
    simp [sampleMatrix,g,V,Matrix.vandermonde]
  rw [hF,hG,det_mul,det_diagonal,det_transpose]
  ring

end OddZetaSix.B40a
