import OddZetaSix.B40a.Arithmetic.PeriodicGrid

noncomputable section
namespace OddZetaSix.B40a
open Finset

private theorem reflect_quotient (v p : ℤ) (hp : 0<p) :
    (-v-1-p)/p = -2-v/p := by
  apply (Int.ediv_eq_iff_of_pos hp).mpr
  have h₁ := Int.ediv_mul_le v hp.ne'
  have h₂ := Int.lt_ediv_add_one_mul_self v hp
  constructor <;> nlinarith

private theorem reflected_count (a b z : ℤ) (n p : ℕ) (hp : 0<p) :
    periodicCount a b ((n:ℝ)/p) ((((p:ℤ)+1-z:ℤ):ℝ)/p) =
    periodicCount (-b) (-a) ((n:ℝ)/p) ((z:ℝ)/p) := by
  rw [periodicCount_rational _ _ _ _ _ hp,periodicCount_rational _ _ _ _ _ hp]
  have H (e : ℤ) : (e*n-((p:ℤ)+1-z))/(p:ℤ) = -2-((-e)*n-z)/(p:ℤ) := by
    rw [←reflect_quotient _ _ (by exact_mod_cast hp : 0<(p:ℤ))]
    congr 1
    ring
  rw [H a,H b,show -a - -b = b-a by ring]
  omega

theorem periodicScore_reflected_sample (n p j : ℕ) (hp : 0<p) (hj : j<p) :
    periodicScore ((n:ℝ)/p) ((((p-1-j:ℕ):ℝ)+1)/p) =
    periodicScore ((n:ℝ)/p) (((j:ℝ)+1)/p) := by
  let z : ℤ := (j:ℤ)+1
  have hz : ((z:ℝ)) = (j:ℝ)+1 := by simp [z]
  have he : (((p-1-j:ℕ):ℝ)+1) = (((p:ℤ)+1-z:ℤ):ℝ) := by
    dsimp [z]; push_cast [Nat.sub_add_cancel (show 1≤p by omega),
      Nat.cast_sub (show j≤p-1 by omega),Nat.cast_sub (show 1≤p by omega)]; ring
  rw [he,←hz]
  unfold periodicScore
  simp only [reflected_count _ _ _ _ _ hp, neg_neg]
  norm_num
  <;> ring_nf

/-- A right-endpoint Riemann sum on the first half of an odd or even grid
costs at most half the complete sum when the reflected samples agree. -/
private theorem sum_first_half_le (g : ℕ → ℝ) (p : ℕ)
    (hg : ∀ j,0 ≤ g j) (hr : ∀ j<p, g (p-1-j)=g j) :
    2*(∑ j ∈ range (p/2),g j) ≤ ∑ j ∈ range p,g j := by
  let d := p/2
  have hd : d≤p-d := by dsimp [d]; omega
  have hdp : p-d+d=p := by dsimp [d]; omega
  have hmid : (∑ j ∈ range d,g ((p-d)+j)) = ∑ j ∈ range d,g j := by
    calc
      _ = ∑ j ∈ range d,g (d-1-j) := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        have harg : p-1-(d-1-j) = (p-d)+j := by omega
        rw [←harg,hr _ (by omega)]
      _ = _ := sum_range_reflect g d
  have hh := sum_range_add g (p-d) d
  rw [hdp,hmid] at hh
  have hpre := sum_le_sum_of_subset_of_nonneg (range_mono hd)
    (fun j _ _ => hg j)
  change 2*(∑ j ∈ range d,g j) ≤ _
  linarith only [hh,hpre]

/-- A true per-prime denominator bound in terms of the continuous full-period
integral. The error is constant on every band p/n ≥ ε > 0. -/
theorem primeExponent_le_full_period_integral (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsq : 84*n<p^2) (ε : ℝ) (hε : 0<ε) (hband : ε*(n:ℝ)≤p) :
    primeExponent n p ≤ (p:ℝ)/2 *
      (∫ u in (0:ℝ)..1, (slotEnvelope (2*fiveRank n/p)
        (periodicScore ((n:ℝ)/p) u).toNat : ℝ)) + (7680/ε+432) := by
  let q := 2*fiveRank n/p
  let F (b : ℤ) : ℝ := slotEnvelope q b.toNat
  let g (j : ℕ) := F (periodicScore ((n:ℝ)/p) (((j:ℝ)+1)/p))
  let S (k : ℕ) := F (periodicScore ((n:ℝ)/p) ((k:ℝ)/p))
  have hp := (Fact.out : p.Prime).pos
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hb := primeExponent_periodic_on_band n p hn hsq ε hε hband
  change primeExponent n p ≤ (∑ c : Fin (p/2+1), S c.val) + _ at hb
  rw [Fin.sum_univ_eq_sum_range, sum_range_succ'] at hb
  simp only [S,Nat.cast_add,Nat.cast_one,Nat.cast_zero] at hb
  have hhalf := sum_first_half_le g p (fun j => Nat.cast_nonneg _)
    (fun j hj => congrArg F (periodicScore_reflected_sample n p j hp hj))
  have hgrid := periodic_grid_integral n p p hp F
  rw [div_self hpR.ne'] at hgrid
  change (∑ j ∈ range p,g j) = _ at hgrid
  rw [hgrid] at hhalf
  have hM : F (periodicScore ((n:ℝ)/p) ((0:ℝ)/p)) ≤ 1280/ε + 72 := by
    have hB := (periodicScore_bounds ((n:ℝ)/p) ((0:ℝ)/p)).2
    have hnat : (periodicScore ((n:ℝ)/p) ((0:ℝ)/p)).toNat ≤ 16 := Int.toNat_le.mpr hB
    have hslot := slotEnvelope_eq_sum q _ hnat
    have hslot16 := slotEnvelope_eq_sum q 16 (by decide)
    have hle : slotEnvelope q (periodicScore ((n:ℝ)/p) ((0:ℝ)/p)).toNat ≤ slotEnvelope q 16 := by
      rw [← hslot,← hslot16]; exact sum_le_sum (fun _ _ => Nat.sub_le_sub_right hnat _)
    have hqNat : q*p ≤ 80*n := (Nat.div_mul_le_self (2*fiveRank n) p).trans
      (by unfold fiveRank; omega)
    have hq : (q:ℝ)*(p:ℝ) ≤ 80*(n:ℝ) := by exact_mod_cast hqNat
    have hqe : (q:ℝ) ≤ 80/ε := by
      apply (le_div_iff₀ hε).mpr
      apply le_of_mul_le_mul_right (a:=(n:ℝ)) _ (by exact_mod_cast hn)
      nlinarith only [mul_le_mul_of_nonneg_left hband (Nat.cast_nonneg q),hq]
    have hh : (slotEnvelope q 16 : ℝ) = 16*(q:ℝ)+72 := by simp [slotEnvelope]; ring
    calc
      _ ≤ (slotEnvelope q 16 : ℝ) := by dsimp [F]; exact_mod_cast hle
      _ ≤ _ := by rw [hh,show (1280:ℝ)/ε=16*(80/ε) by ring]; linarith
  change primeExponent n p ≤ (∑ j ∈ range (p/2),g j) + F (periodicScore ((n:ℝ)/p) ((0:ℝ)/p)) + _ at hb
  change primeExponent n p ≤ _/2 * (∫ u in (0:ℝ)..1,F (periodicScore ((n:ℝ)/p) u)) + _
  rw [show (7680:ℝ)/ε=6400/ε+1280/ε by ring]
  linarith only [hb,hhalf,hM]

end OddZetaSix.B40a
