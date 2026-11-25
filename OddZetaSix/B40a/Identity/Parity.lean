import OddZetaSix.B40a.Identity.Kernel
import Mathlib.Tactic

/-! B40a adaptation of the partial-fraction argument in the upstream
OddZetaSix.SixIdentity module. The upstream project is MIT licensed. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators Topology
def kernelReflectedPole (n k : ℕ) : ℕ := 118 * n + 2 - k

private theorem interval_list_count (a d k : ℕ) :
    ((List.range (d + 1)).map (fun j => a + j)).count k =
      if a ≤ k ∧ k ≤ a + d then 1 else 0 := by
  have hmem : k ∈ (List.range (d + 1)).map (fun j => a + j) ↔
      a ≤ k ∧ k ≤ a + d := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨hk, hd⟩
      exact ⟨k - a, by omega, by omega⟩
  split_ifs with h
  · apply List.count_eq_one_of_mem
    · exact (List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr
        List.nodup_range
    · exact hmem.mpr h
  · exact List.count_eq_zero_of_not_mem (fun hk => h (hmem.mp hk))

theorem kernel_pole_order_reflection (n k : ℕ) :
    kernelPoleOrder n (kernelReflectedPole n k) = kernelPoleOrder n k := by
  unfold kernelPoleOrder kernelPoleList
  rw [list_count_flatMap, list_count_flatMap]
  congr 1
  apply List.map_congr_left
  intro b _
  have hb : 2*kernelOffset b ≤ 50 := offset_le b
  rw [interval_list_count, interval_list_count]
  have hsub : 50 - 2 * kernelOffset b + 2 * kernelOffset b = 50 := by omega
  have hend : 2 * ((34 + kernelOffset b) * n + 1) + (50 - 2 * kernelOffset b) * n = 118 * n + 2 := by
    nlinarith
  have hiff : ((34 + kernelOffset b) * n + 1 ≤ kernelReflectedPole n k ∧
      kernelReflectedPole n k ≤ (34 + kernelOffset b) * n + 1 + (50 - 2 * kernelOffset b) * n) ↔
      ((34 + kernelOffset b) * n + 1 ≤ k ∧
        k ≤ (34 + kernelOffset b) * n + 1 + (50 - 2 * kernelOffset b) * n) := by
    unfold kernelReflectedPole
    omega
  simp only [hiff]

theorem kernel_pole_mem_reflection (n k : ℕ) :
    kernelReflectedPole n k ∈ kernelPoleSet n ↔ k ∈ kernelPoleSet n := by
  have hmem (a : ℕ) : a ∈ kernelPoleSet n ↔ 0 < kernelPoleOrder n a := by
    simp only [kernelPoleSet, kernelPoleOrder, List.mem_toFinset, List.count_pos_iff]
  rw [hmem, hmem, kernel_pole_order_reflection]

theorem kernel_pole_reflection_involutive (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    kernelReflectedPole n (kernelReflectedPole n k) = k := by
  have hb := kernel_pole_address_bounds n k hk
  unfold kernelReflectedPole
  omega

theorem kernel_sum_reflection {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ k ∈ kernelPoleSet n, f (kernelReflectedPole n k)) =
      ∑ k ∈ kernelPoleSet n, f k := by
  apply Finset.sum_bij (fun k _ => kernelReflectedPole n k)
  · intro k hk
    exact (kernel_pole_mem_reflection n k).mpr hk
  · intro k hk l hl h
    have := congrArg (kernelReflectedPole n) h
    simpa only [kernel_pole_reflection_involutive n k hk,
      kernel_pole_reflection_involutive n l hl] using this
  · intro k hk
    exact ⟨kernelReflectedPole n k, (kernel_pole_mem_reflection n k).mpr hk,
      kernel_pole_reflection_involutive n k hk⟩
  · intros
    rfl

theorem kernel_pole_factor_reflection (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    (X + C (k : ℚ)).comp (-X - C (118 * (n : ℚ) + 2)) =
      -(X + C (kernelReflectedPole n k : ℚ)) := by
  have hb := kernel_pole_address_bounds n k hk
  have hle : k ≤ 118 * n + 2 := by omega
  simp only [kernelReflectedPole, Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, add_comp, X_comp, C_comp, map_sub, map_add, map_mul, map_ofNat]
  ring

theorem kernelPoleComplement_reflection (n k l : ℕ) (hk : k ∈ kernelPoleSet n)
    (hl : l < kernelPoleOrder n k) :
    (kernelPoleComplement n k l).comp (-X - C (118 * (n : ℚ) + 2)) =
      (-1 : ℚ[X]) ^ (l + 1) * kernelPoleComplement n (kernelReflectedPole n k) l := by
  have hr := (kernel_pole_mem_reflection n k).mpr hk
  have hlr : l < kernelPoleOrder n (kernelReflectedPole n k) := by
    rwa [kernel_pole_order_reflection]
  have h := congrArg (fun p : ℚ[X] => p.comp (-X - C (118 * (n : ℚ) + 2)))
    (kernelPoleComplement_mul n k l hk hl)
  rw [mul_comp, pow_comp, kernel_pole_factor_reflection n k hk,
    kernelDenominator_reflection, ← kernelPoleComplement_mul n _ l hr hlr] at h
  have hs : (-1 : ℚ[X]) ^ (l + 1) * (-1 : ℚ[X]) ^ (l + 1) = 1 := by
    rw [← mul_pow]
    simp
  apply mul_left_cancel₀ ((monic_X_add_C (kernelReflectedPole n k : ℚ)).pow (l + 1)).ne_zero
  rw [neg_pow] at h
  have h' := congrArg (fun p : ℚ[X] => (-1) ^ (l + 1) * p) h
  calc
    _ = ((-1 : ℚ[X]) ^ (l + 1) * (-1 : ℚ[X]) ^ (l + 1)) *
        ((X + C (kernelReflectedPole n k : ℚ)) ^ (l + 1) *
          (kernelPoleComplement n k l).comp (-X - C (118 * (n : ℚ) + 2))) := by
      rw [hs, one_mul]
    _ = _ := by linear_combination h'

/-- Reflection sends the coefficient at `k` (pole order `l + 1`) to `(-1)^l` times
the coefficient at `2 c_n - k`. -/
theorem kernel_principal_coefficients_reflection (n : ℕ) (i j : Fin (kernelRank n))
    (k : ℕ) (hk : k ∈ kernelPoleSet n) (l : Fin (kernelPoleOrder n k)) :
    kernelPrincipalCoefficients n i j k l = (-1 : ℚ) ^ l.val *
      kernelPrincipalCoefficients n i j (kernelReflectedPole n k)
        (l.cast (kernel_pole_order_reflection n k).symm) := by
  let b : (a : ℕ) → Fin (kernelPoleOrder n a) → ℚ := fun a t =>
    (-1 : ℚ) ^ t.val * kernelPrincipalCoefficients n i j (kernelReflectedPole n a)
      (t.cast (kernel_pole_order_reflection n a).symm)
  let F := C (kernelNormalization n) * kernelNumerator n * kernelCenteredMultiplier n i j
  let phi : ℚ[X] := -X - C (118 * (n : ℚ) + 2)
  have hneg : F = ∑ a ∈ kernelPoleSet n, ∑ t,
      -(C (kernelPrincipalCoefficients n i j a t) *
        (kernelPoleComplement n a t.val).comp phi) := by
    have h := congrArg (fun p : ℚ[X] => -(p.comp phi))
      (kernel_cleared_partial_fractions n i j)
    simpa only [F, phi, Polynomial.sum_comp, mul_comp, C_comp,
      kernelNumerator_reflection, centeredMultiplier_reflection,
      mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib] using h
  have hnum : F = ∑ a ∈ kernelPoleSet n, ∑ t,
      C (b a t) * kernelPoleComplement n a t.val := by
    calc
      F = ∑ a ∈ kernelPoleSet n, ∑ t,
          -(C (kernelPrincipalCoefficients n i j a t) *
            (kernelPoleComplement n a t.val).comp phi) := hneg
      _ = ∑ a ∈ kernelPoleSet n, ∑ t,
          -(C (kernelPrincipalCoefficients n i j (kernelReflectedPole n a) t) *
            (kernelPoleComplement n (kernelReflectedPole n a) t.val).comp phi) :=
        (kernel_sum_reflection n (fun a => ∑ t,
          -(C (kernelPrincipalCoefficients n i j a t) *
            (kernelPoleComplement n a t.val).comp phi))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Fintype.sum_equiv (finCongr (kernel_pole_order_reflection n a))
        intro t
        have hr := (kernel_pole_mem_reflection n a).mpr ha
        rw [show phi = -X - C (118 * (n : ℚ) + 2) from rfl,
          kernelPoleComplement_reflection n _ t.val hr t.isLt,
          kernel_pole_reflection_involutive n a ha]
        simp only [b, finCongr_apply, Fin.cast_cast, Fin.cast_refl,
          id_eq, Fin.val_cast, map_mul, map_pow, map_neg, map_one, pow_succ]
        ring
  have hclear (a : (k : ℕ) → Fin (kernelPoleOrder n k) → ℚ) :
      algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) *
        (∑ k ∈ kernelPoleSet n, ∑ t, kernelPrincipalTerm k t.val (a k t)) =
      algebraMap ℚ[X] (RatFunc ℚ) (∑ k ∈ kernelPoleSet n, ∑ t,
        C (a k t) * kernelPoleComplement n k t.val) := by
    simp only [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro t _
    exact kernelPrincipalTerm_clear n k t.val hk t.isLt _
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (kernelDenominator n) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (kernelDenominator_monic n).ne_zero
  have heq : (∑ k ∈ kernelPoleSet n, ∑ t,
      kernelPrincipalTerm k t.val (kernelPrincipalCoefficients n i j k t)) =
      ∑ k ∈ kernelPoleSet n, ∑ t, kernelPrincipalTerm k t.val (b k t) := by
    apply mul_left_cancel₀ hd
    rw [hclear, hclear, ← kernel_cleared_partial_fractions n i j, ← hnum]
  exact congrFun (kernel_principal_coefficients_unique n
    (kernelPrincipalCoefficients n i j) b heq k hk) l

def kernelAggregatePrincipalCoefficient (n : ℕ) (i j : Fin (kernelRank n)) (m : ℕ) : ℚ :=
  ∑ k ∈ kernelPoleSet n, ∑ l,
    if l.val + 1 = m then kernelPrincipalCoefficients n i j k l else 0

/-- Every even pole order cancels (eliminating all even zeta values). -/
theorem kernel_even_pole_sum_zero (n : ℕ) (i j : Fin (kernelRank n)) (m : ℕ) (hm : Even m) :
    kernelAggregatePrincipalCoefficient n i j m = 0 := by
  let A := kernelAggregatePrincipalCoefficient n i j m
  have hsign (v : ℕ) (hv : v + 1 = m) : (-1 : ℚ) ^ v = -1 := by
    have hvodd : Odd v := by
      obtain ⟨a, ha⟩ := hm
      exact ⟨a - 1, by omega⟩
    exact hvodd.neg_one_pow
  have hA : A = -A := by
    calc
      A = ∑ k ∈ kernelPoleSet n, ∑ l,
          if l.val + 1 = m then
            kernelPrincipalCoefficients n i j (kernelReflectedPole n k) l else 0 :=
        (kernel_sum_reflection n (fun k => ∑ l : Fin (kernelPoleOrder n k),
          if l.val + 1 = m then kernelPrincipalCoefficients n i j k l else 0)).symm
      _ = ∑ k ∈ kernelPoleSet n, ∑ l,
          -(if l.val + 1 = m then kernelPrincipalCoefficients n i j k l else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Fintype.sum_equiv (finCongr (kernel_pole_order_reflection n k))
        intro l
        have hc := kernel_principal_coefficients_reflection n i j k hk
          (l.cast (kernel_pole_order_reflection n k))
        simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.val_cast] at hc
        simp only [finCongr_apply, Fin.val_cast]
        by_cases hl : l.val + 1 = m
        · rw [hsign l.val hl, neg_one_mul] at hc
          simp only [hl, ite_true]
          linarith
        · simp only [hl, ite_false, neg_zero]
      _ = -A := by
        simp only [Finset.sum_neg_distrib, A, kernelAggregatePrincipalCoefficient]
  change A = 0
  linarith

theorem kernel_aggregate_simple_zero (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelAggregatePrincipalCoefficient n i j 1 = 0 := by
  simpa [kernelAggregatePrincipalCoefficient] using kernel_residue_sum_zero n i j

theorem kernel_aggregate_above_fourteen_zero (n : ℕ) (i j : Fin (kernelRank n))
    (m : ℕ) (hm : 12 < m) : kernelAggregatePrincipalCoefficient n i j m = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  have horder := kernel_pole_order_le n k
  have hl := l.isLt
  rw [ite_eq_right (by omega)]

/-- Only pole orders `{3, 5, 7, 9, 11}` can survive, giving exactly
`ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)` after four derivatives. -/
theorem kernel_aggregate_support (n : ℕ) (i j : Fin (kernelRank n)) (m : ℕ)
    (hm : m ∉ ({3, 5, 7, 9, 11} : Finset ℕ)) :
    kernelAggregatePrincipalCoefficient n i j m = 0 := by
  by_cases h1 : m = 1
  · subst m
    exact kernel_aggregate_simple_zero n i j
  by_cases he : Even m
  · exact kernel_even_pole_sum_zero n i j m he
  apply kernel_aggregate_above_fourteen_zero n i j m
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rw [Nat.even_iff] at he
  omega

theorem kernel_odd_index_sum_zero (n : ℕ) (i j : Fin (kernelRank n)) (s : ℕ) (hs : Odd s) :
    (∑ k ∈ kernelPoleSet n, ∑ l,
      if l.val = s then kernelPrincipalCoefficients n i j k l else 0) = 0 := by
  have he : Even (s + 1) := by
    obtain ⟨a, ha⟩ := hs
    exact ⟨a + 1, by omega⟩
  simpa [kernelAggregatePrincipalCoefficient] using kernel_even_pole_sum_zero n i j (s + 1) he

/-! ## Rational coefficients and five-variable affine moment matrix -/

/-- Index `s` corresponds to `ζ(s + 5)` (pole order `s + 1`). -/
def kernelOrderCoefficient (n : ℕ) (i j : Fin (kernelRank n)) (s : ℕ) : ℚ :=
  ∑ k ∈ kernelPoleSet n, ∑ l,
    if l.val = s then kernelPrincipalCoefficients n i j k l else 0

def kernelZetaCoefficient (n : ℕ) (i j : Fin (kernelRank n)) (s : ℕ) : ℚ :=
  ((s + 4).choose 4 : ℚ) * kernelOrderCoefficient n i j s

def kernelMomentConstant (n : ℕ) (i j : Fin (kernelRank n)) : ℚ :=
  -(∑ k ∈ kernelPoleSet n, ∑ l,
    kernelPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
      harmonicCutoff (l.val + 5) (k - 25 * n - 1))

theorem kernelOrderCoefficient_zero (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelOrderCoefficient n i j 0 = 0 := kernel_residue_sum_zero n i j

/-- The `ζ(5)` coefficient is strictly zero. -/
theorem kernelZetaCoefficient_zero (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelZetaCoefficient n i j 0 = 0 := by
  simp [kernelZetaCoefficient, kernelOrderCoefficient_zero]

/-- Every even-weight zeta coefficient (`s` odd, i.e. `s + 5` even) is strictly zero. -/
theorem kernelZetaCoefficient_odd (n : ℕ) (i j : Fin (kernelRank n)) (s : ℕ) (hs : Odd s) :
    kernelZetaCoefficient n i j s = 0 := by
  simp [kernelZetaCoefficient, kernelOrderCoefficient, kernel_odd_index_sum_zero n i j s hs]

theorem kernel_order_regroup (n : ℕ) (i j : Fin (kernelRank n)) (z : ℕ → ℝ) :
    (∑ s : Fin 12, (kernelZetaCoefficient n i j s : ℝ) * z s) =
      ∑ k ∈ kernelPoleSet n, ∑ l,
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) * z l.val := by
  simp only [kernelZetaCoefficient, kernelOrderCoefficient, Rat.cast_mul, Rat.cast_sum,
    Rat.cast_natCast, apply_ite, Rat.cast_zero, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  let s : Fin 12 := ⟨l.val, l.isLt.trans_le (kernel_pole_order_le n k)⟩
  rw [Finset.sum_eq_single s]
  · simp only [s, ite_true]
    ring
  · intro b _ hbs
    have hne : l.val ≠ b.val := by
      intro he
      exact hbs (Fin.ext he.symm)
    simp [hne]
  · simp

theorem kernel_complete_sum_regroup (n : ℕ) (i j : Fin (kernelRank n)) (z : ℕ → ℝ) :
    (kernelMomentConstant n i j : ℝ) +
        (∑ s : Fin 12, (kernelZetaCoefficient n i j s : ℝ) * z s) =
      ∑ k ∈ kernelPoleSet n, ∑ l,
        (kernelPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (z l.val - (harmonicCutoff (l.val + 5) (k - 25 * n - 1) : ℝ)) := by
  rw [kernel_order_regroup]
  simp only [kernelMomentConstant, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_natCast, mul_sub, Finset.sum_sub_distrib]
  ring

theorem kernel_coordinate_reduction (n : ℕ) (i j : Fin (kernelRank n)) (z : ℕ → ℝ) :
    (∑ s : Fin 12, (kernelZetaCoefficient n i j s : ℝ) * z (s.val + 5)) =
      ∑ s : Fin 5, (kernelZetaCoefficient n i j (2 + 2 * s.val) : ℝ) * z (7 + 2 * s.val) := by
  have hz (s : ℕ) : kernelZetaCoefficient n i j (2 * s + 1) = 0 :=
    kernelZetaCoefficient_odd n i j (2 * s + 1) ⟨s, by omega⟩
  have h1 := hz 0
  have h3 := hz 1
  have h5 := hz 2
  have h7 := hz 3
  have h9 := hz 4
  have h11 := hz 5
  norm_num [Fin.sum_univ_succ, kernelZetaCoefficient_zero, h1, h3, h5, h7, h9, h11]

/-- Fourth-derivative partial-fraction identity: every entry of `𝓗_n(ζ)` is an
exact affine rational combination of `ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)`. -/
theorem kernelFunctional_eq_five (n : ℕ) (i j : Fin (kernelRank n)) :
    kernelFunctional n i j = (kernelMomentConstant n i j : ℝ) +
      ∑ s : Fin 5, (kernelZetaCoefficient n i j (2 + 2 * s.val) : ℝ) * fiveValues s := by
  rw [kernelFunctional_eq_pole_sum,
    ← kernel_complete_sum_regroup n i j (fun s => zetaNat (s + 5)),
    kernel_coordinate_reduction]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [fiveValues, zetaNat_eq_re_riemannZeta (by omega : 2 ≤ 7+2*s.val)]


end OddZetaSix.B40a
