import OddZetaSix.B40a.Arithmetic.PeriodicWallCost

/-! Exact quadrature on the residue grid. Each floor changes only at a grid
boundary and its value there is its limit from the left. -/
noncomputable section
namespace OddZetaSix.B40a
open Set MeasureTheory Finset

private theorem grid_floor (e : ℤ) (n p j : ℕ) (hp : 0<p) {u : ℝ}
    (hu : u ∈ Ioc ((j:ℝ)/p) (((j:ℝ)+1)/p)) :
    ⌊(e:ℝ)*((n:ℝ)/p)-u⌋ = (e*(n:ℤ)-((j:ℤ)+1))/(p:ℤ) := by
  let m := e*(n:ℤ)-((j:ℤ)+1)
  let k := m/(p:ℤ)
  have hpz : 0 < (p:ℤ) := by exact_mod_cast hp
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have h1 : k*(p:ℤ) ≤ m := Int.ediv_mul_le m hpz.ne'
  have h2 : m+1 ≤ (k+1)*(p:ℤ) := Int.add_one_le_of_lt (Int.lt_ediv_add_one_mul_self m hpz)
  have h1r : (k:ℝ)*(p:ℝ) ≤ (e:ℝ)*n-((j:ℝ)+1) := by exact_mod_cast h1
  have h2r : (e:ℝ)*n-((j:ℝ)+1)+1 ≤ ((k:ℝ)+1)*p := by exact_mod_cast h2
  have hl := (div_lt_iff₀ hpR).mp hu.1
  have hr := (le_div_iff₀ hpR).mp hu.2
  apply Int.floor_eq_iff.mpr
  rw [show (e:ℝ)*((n:ℝ)/p)-u = ((e:ℝ)*n-u*p)/p by field_simp]
  exact ⟨(le_div_iff₀ hpR).mpr (by linarith), (div_lt_iff₀ hpR).mpr (by linarith)⟩

theorem periodicScore_on_grid_cell (n p j : ℕ) (hp : 0<p) {u : ℝ}
    (hu : u ∈ Ioc ((j:ℝ)/p) (((j:ℝ)+1)/p)) :
    periodicScore ((n:ℝ)/p) u = periodicScore ((n:ℝ)/p) (((j:ℝ)+1)/p) := by
  have hight : (((j:ℝ)+1)/p) ∈ Ioc ((j:ℝ)/p) (((j:ℝ)+1)/p) :=
    ⟨div_lt_div_of_pos_right (by linarith) (by exact_mod_cast hp),le_rfl⟩
  have h (e : ℤ) := (grid_floor e n p j hp hu).trans (grid_floor e n p j hp hight).symm
  unfold periodicScore periodicCount
  simp only [h]

/-- Applies to any transform of the integer score. This includes both the
linear slot count and the quadratic tail, without a variation error. -/
theorem periodic_grid_integral (n p m : ℕ) (hp : 0<p) (F : ℤ → ℝ) :
    (∑ j ∈ range m, F (periodicScore ((n:ℝ)/p) (((j:ℝ)+1)/p))) =
      (p:ℝ) * ∫ u in 0..((m:ℝ)/p), F (periodicScore ((n:ℝ)/p) u) := by
  let x (i : ℕ) : ℝ := i/p
  let g (u : ℝ) := F (periodicScore ((n:ℝ)/p) u)
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hx (j : ℕ) : x (j+1) = ((j:ℝ)+1)/p := by simp [x]
  have hab (j : ℕ) : x j ≤ x (j+1) := by rw [hx]; exact div_le_div_of_nonneg_right (by linarith) hpR.le
  have cell (j : ℕ) : EqOn g (fun _ => g (x (j+1))) (Ioo (x j) (x (j+1))) := by
    intro t ht
    dsimp [g]
    rw [hx]
    apply congrArg F
    apply periodicScore_on_grid_cell n p j hp
    exact ⟨ht.1,by rw [←hx]; exact ht.2.le⟩
  have integrable (j : ℕ) : IntervalIntegrable g volume (x j) (x (j+1)) := by
    apply (intervalIntegrable_congr_uIoo (uIoo_of_le (hab j) ▸ cell j)).mpr
    exact intervalIntegrable_const
  have eq (j : ℕ) : (∫ u in x j..x (j+1), g u) = g (x (j+1))/p := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (hab j) (cell j),intervalIntegral.integral_const,
      smul_eq_mul,hx]
    dsimp [x]
    ring
  have H := intervalIntegral.sum_integral_adjacent_intervals (n:=m)
    (fun j _ => integrable j)
  simp_rw [eq] at H
  rw [← sum_div] at H
  have xx : x 0 = 0 := by simp [x]
  rw [xx] at H
  simp only [hx] at H
  change _ = (p:ℝ)*(∫ u in 0..x m, g u)
  rw [←H, mul_div_cancel₀ _ hpR.ne']

end OddZetaSix.B40a
