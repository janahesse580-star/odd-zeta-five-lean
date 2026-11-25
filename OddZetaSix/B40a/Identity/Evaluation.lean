import OddZetaSix.B40a.Identity.Taylor

noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

private theorem rat_map_eq : algebraMap ℚ ℝ = Rat.castHom ℝ := RingHom.ext_rat _ _

theorem sum_orders {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    (∑ k ∈ Icc 1 m, f k) = ∑ l : Fin m, f (l.val+1) := by
  let toFin (k : ℕ) (hk : k ∈ Icc 1 m) : Fin m :=
    ⟨k-1, by have := mem_Icc.mp hk; omega⟩
  apply Finset.sum_bij toFin
  · intro k hk
    exact mem_univ _
  · intro k hk l hl h
    have hh := congrArg Fin.val h
    have hk' := mem_Icc.mp hk
    have hl' := mem_Icc.mp hl
    dsimp [toFin] at hh
    omega
  · intro l _
    have hl : l.val+1 ∈ Icc 1 m := by rw [mem_Icc]; have := l.isLt; omega
    refine ⟨l.val+1,hl,?_⟩
    apply Fin.ext
    simp [toFin]
  · intro k hk
    have hk' := mem_Icc.mp hk
    simp only [toFin]
    congr 1
    omega

private theorem kernelEntryReal_eq (n i j : ℕ) :
    kernelEntryReal n i j = entryKernel n i j := by
  funext x
  unfold kernelEntryReal entryKernel kernelCenteredMultiplier
  have hh : (59 * (n : ℚ) + 1 : ℚ) = (center n : ℚ) := by
    unfold center
    push_cast
    ring
  rw [hh]
  simp only [kernelNormalization,kernelNumerator,kernelDenominator,map_mul,
    aeval_C, aeval_comp, map_add, aeval_X, map_natCast]
  simp only [aeval_def, rat_map_eq, Rat.coe_castHom]
  ring

theorem fiveFunctional_eq_kernel (n : ℕ) (i j : Fin (fiveRank n)) :
    fiveFunctional n i j = kernelFunctional n i j := by
  unfold fiveFunctional kernelFunctional
  rw [kernelEntryReal_eq]

private theorem zetaSymbol_eval (l : ℕ) :
    (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) fiveValues) (zetaSymbol (l+1)) =
      ∑ s : Fin 5, if l = 2+2*s.val then fiveValues s else 0 := by
  rw [zetaSymbol,map_sum]
  apply sum_congr rfl
  intro s _
  have he : l+1 = 3+2*s.val ↔ l=2+2*s.val := by omega
  by_cases h : l = 2+2*s.val
  · simp only [ite_eq_left (he.mpr h), ite_eq_left h, MvPolynomial.eval₂Hom_X']
  · simp only [ite_eq_right (fun h' => h (he.mp h')), ite_eq_right h, map_zero]

theorem harmonic_eq (s m : ℕ) : lowerHarmonic s m = harmonicCutoff s m := by
  unfold lowerHarmonic harmonicCutoff
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Nat.cast_add,Nat.cast_one] using sum_orders m (fun v => 1/(v : ℚ)^s)

theorem Hpoly_entry_eval (n : ℕ) (i j : Fin (fiveRank n)) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) fiveValues (Hpoly n i j) = fiveFunctional n i j := by
  rw [fiveFunctional_eq_kernel,kernelFunctional_eq_five]
  have hp :
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) fiveValues) (Hpoly n i j) =
      ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ)*((l.val+4).choose 4 : ℝ)*
        ((∑ s : Fin 5, if l.val=2+2*s.val then fiveValues s else 0) -
             (harmonicCutoff (l.val+5) (k-25*n-1) : ℝ)) := by
    unfold Hpoly fiveEntry
    rw [map_sum,← kernelPoleSet_eq_poleList]
    apply sum_congr rfl
    intro k hk
    rw [← kernelPoleOrder_eq_poleOrder,map_sum,sum_orders]
    apply sum_congr rfl
    intro l _
    rw [map_mul,map_sub,MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C,
      localPrincipal_eq n i j k hk l,zetaSymbol_eval,harmonic_eq]
    simp only [rat_map_eq, Rat.coe_castHom,
      Nat.add_assoc, Nat.reduceAdd, Rat.cast_mul, Rat.cast_natCast]
    ring
  change (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) fiveValues) (Hpoly n i j) = _
  rw [hp]
  simp only [mul_sub, sum_sub_distrib, kernelMomentConstant, Rat.cast_neg, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast]
  rw [sub_eq_neg_add]
  congr 1
  simp only [mul_sum, kernelZetaCoefficient, kernelOrderCoefficient, Rat.cast_mul, Rat.cast_sum,
    Rat.cast_natCast]
  calc
    _ = ∑ k ∈ kernelPoleSet n, ∑ s : Fin 5, ∑ l : Fin (kernelPoleOrder n k),
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val+4).choose 4 : ℝ) *
          (if l.val=2+2*s.val then fiveValues s else 0) := by
      apply sum_congr rfl
      intro k _
      exact sum_comm
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      simp only [sum_mul]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro l _
      by_cases hh : l.val=2+2*s.val
      · simp [hh,mul_comm]
      · simp only [ite_eq_right hh, Rat.cast_zero, mul_zero, zero_mul]

/-- The polynomial used by Stage 1 evaluates to the actual B40a determinant. -/
theorem Hpoly_det_eval (n : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) fiveValues (Hpoly n).det = (fiveFunctional n).det := by
  change (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) fiveValues) (Hpoly n).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact Hpoly_entry_eval n i j

end OddZetaSix.B40a
