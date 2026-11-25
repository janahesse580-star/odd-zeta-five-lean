import OddZetaSix.SixPNTBridge
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace OddZetaSix.B40a

open Filter
open scoped Topology BigOperators

/-- Normalized count in a shifted residue class, less the factorial count. -/
noncomputable def periodicCount (a b : ℤ) (τ u : ℝ) : ℤ :=
  ⌊(b : ℝ)*τ-u⌋ - ⌊(a : ℝ)*τ-u⌋ - ⌊((b-a : ℤ) : ℝ)*τ⌋

theorem periodicCount_add_int (a b k : ℤ) (τ u : ℝ) :
    periodicCount a b (τ+k) u = periodicCount a b τ u := by
  have sh (e : ℤ) (x : ℝ) :
      (e : ℝ)*(τ+k)-x = (e : ℝ)*τ-x + ((e*k : ℤ) : ℝ) := by
    push_cast
    ring
  have sh' : (((b-a : ℤ) : ℝ) * (τ+k)) =
      (((b-a : ℤ) : ℝ) * τ) + (((b-a)*k : ℤ) : ℝ) := by
    push_cast
    ring
  unfold periodicCount
  rw [sh a,sh b,sh',Int.floor_add_intCast,Int.floor_add_intCast,Int.floor_add_intCast]
  ring

noncomputable def periodicScore (τ u : ℝ) : ℤ :=
  max 0 (4 + 6*periodicCount (-25) 25 τ u + 4*periodicCount (-17) 17 τ u +
    2*periodicCount (-16) 16 τ u - 5*periodicCount (-59) (-34) τ u -
    5*periodicCount 34 59 τ u)

theorem periodicScore_add_int (k : ℤ) (τ u : ℝ) :
    periodicScore (τ+k) u = periodicScore τ u := by
  simp only [periodicScore, periodicCount_add_int]

/-- The first-layer factor used for the inverse-prime-scale majorant. -/
theorem floor_envelope {P F G : ℝ} (hP : 0 < P) (hF : 0 ≤ F) :
    P * ((⌊80/P⌋ + 1 : ℝ)*F+G)/4000 ≤ F/50+P*(F+G)/4000 := by
  have h : (⌊80/P⌋ : ℝ) ≤ 80/P := Int.floor_le _
  have hm : (⌊80/P⌋ : ℝ)*P ≤ 80 :=
    (le_div_iff₀ hP).mp h
  have hmul := mul_le_mul_of_nonneg_right hm hF
  nlinarith only [hmul]

/-- Removing an arbitrarily small cutoff after taking the large-index limit.
The error sequence can be the contribution of higher prime powers. -/
theorem remove_cutoff {f error : ℕ → ℝ} {C B : ℝ} (hB : 0 ≤ B)
    (herr : Tendsto error atTop (𝓝 0))
    (hcut : ∀ ε > 0, ε ≤ 11/20 → ∀ δ > 0,
      ∀ᶠ n in atTop, f n ≤ C + B*ε + δ + error n) :
    ∀ δ > 0, ∀ᶠ n in atTop, f n ≤ C+δ := by
  intro δ hδ
  let ε := min (11/20 : ℝ) (δ/(4*(B+1)))
  have hB1 : 0 < B+1 := by linarith
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε' : ε ≤ 11/20 := min_le_left _ _
  have hmul : B*ε ≤ δ/4 := by
    have hd : ε ≤ δ/(4*(B+1)) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 4*(B+1) by positivity)).mp hd
    nlinarith only [hh,hε.le]
  have he := herr.eventually (gt_mem_nhds (show (0 : ℝ) < δ/4 by positivity))
  filter_upwards [hcut ε hε hε' (δ/4) (by positivity),he] with n hn he
  exact le_of_lt (show f n < C+δ by linarith)

/-- Exact contribution from the higher powers, up to the fixed size bound. -/
noncomputable def higherPowerCost (n : ℕ) : ℝ :=
  (640*(n : ℝ)) *
    ∑ p ∈ (Finset.range (Nat.sqrt (84*n)+1)).filter Nat.Prime,
      ((Nat.log p (84*n)-1 : ℕ) : ℝ) * Real.log p

theorem higherPowerCost_nonneg (n : ℕ) : 0 ≤ higherPowerCost n := by
  unfold higherPowerCost
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))

theorem higherPowerCost_rate_zero :
    Tendsto (fun n : ℕ => higherPowerCost n / (2000*(n : ℝ)^2)) atTop (𝓝 0) := by
  have hlim := OddZetaSix.sqrt_mul_log_div_nat_tendsto_zero
  refine squeeze_zero' (Eventually.of_forall fun n =>
    div_nonneg (higherPowerCost_nonneg _) (by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (55 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log (84 * (n : ℝ)) ≤ 2*Real.log (55 * (n : ℝ)) := by
    have hpowlog : Real.log ((55 * (n : ℝ))^2) = 2*Real.log (55*(n : ℝ)) := by
      simpa using Real.log_pow (55*(n : ℝ)) 2
    rw [← hpowlog]
    apply Real.log_le_log (by positivity)
    nlinarith [mul_nonneg hnpos.le (sub_nonneg.mpr hn1)]
  let s := (Finset.range (Nat.sqrt (84*n)+1)).filter Nat.Prime
  have hsize : (s.card : ℝ) ≤ (Nat.sqrt (140*n+2)+1 : ℕ) := by
    exact_mod_cast ((Finset.card_filter_le _ _).trans
      (by simpa using Nat.succ_le_succ (Nat.sqrt_le_sqrt (show 84*n ≤ 140*n+2 by omega))))
  have hsum :
      (∑ p ∈ s, ((Nat.log p (84*n)-1 : ℕ) : ℝ) * Real.log p) ≤
        (Nat.sqrt (140*n+2)+1 : ℕ) * (2*Real.log (55*(n : ℝ))) := by
    calc
      _ ≤ ∑ _p ∈ s, 2 * Real.log (55*(n : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpr := (Finset.mem_filter.mp hp).2
        have hpR : (0 : ℝ) < p := by exact_mod_cast hpr.pos
        have hpn : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
        have hpow : (p : ℝ)^Nat.log p (84*n) ≤ (84 : ℝ)*n := by
          exact_mod_cast Nat.pow_log_le_self p (show 84*n ≠ 0 by positivity)
        have hpLog := Real.log_le_log (by positivity : 0 < (p : ℝ)^Nat.log p (84*n)) hpow
        rw [Real.log_pow] at hpLog
        have hh : ((Nat.log p (84*n)-1 : ℕ) : ℝ) ≤ (Nat.log p (84*n) : ℝ) :=
          by exact_mod_cast Nat.sub_le _ _
        exact (mul_le_mul_of_nonneg_right hh (Real.log_nonneg hpn)).trans (hpLog.trans hlog)
      _ = (s.card : ℝ) * (2*Real.log (55*(n : ℝ))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize (by positivity)
  have hnum :
      higherPowerCost n ≤ (640*(n : ℝ)) *
          ((Nat.sqrt (140*n+2)+1 : ℕ) * (2*Real.log (55*(n : ℝ)))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  apply (div_le_div_of_nonneg_right hnum (by positivity)).trans
  have heq :
      (640*(n : ℝ)) * ((Nat.sqrt (140*n+2)+1 : ℕ) * (2*Real.log (55*(n : ℝ)))) /
          (2000*(n : ℝ)^2) =
        (16/25 : ℝ) *
          ((Nat.sqrt (140*n+2)+1 : ℕ) * Real.log (55*(n : ℝ)) / (n : ℝ)) := by
    field_simp [hnpos.ne']
    <;> ring
  rw [heq]
  have hnneg : 0 ≤ ((Nat.sqrt (140*n+2)+1 : ℕ) : ℝ) *
        Real.log (55*(n : ℝ)) / (n : ℝ) := by positivity
  exact mul_le_of_le_one_left hnneg (by norm_num)


/-- The contribution of all layers above the first can be written as a sum
over primes up to the square root, with no loss from dropping larger primes. -/
theorem higher_power_support {n p : ℕ} (hn : 0<n) (hp : p.Prime)
    (h : 0 < Nat.log p (84*n)-1) : p ≤ Nat.sqrt (84*n) := by
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_log_iff_pow_le hp.one_lt (by omega : 84*n ≠ 0)).mp
  omega

theorem higher_power_full_sum_eq (n : ℕ) (hn : 0<n) :
    (640*(n : ℝ)) *
      (∑ p ∈ (Finset.range (84*n+1)).filter Nat.Prime,
        ((Nat.log p (84*n)-1 : ℕ) : ℝ) * Real.log p) = higherPowerCost n := by
  unfold higherPowerCost
  congr 1
  symm
  apply Finset.sum_subset
  · intro x hx
    have ht := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,ht.2⟩
    have h := Nat.sqrt_le_self (84*n)
    have hx' := Finset.mem_range.mp ht.1
    omega
  · intro p hp hpout
    have hpr := (Finset.mem_filter.mp hp).2
    have hz : Nat.log p (84*n)-1 = 0 := by
      by_contra h
      have hle := higher_power_support hn hpr (Nat.pos_of_ne_zero h)
      exact hpout (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hpr⟩)
    simp [hz]

/-- The two translated tail bounds used by the integer certificate, termwise.
They telescope over any finite interval beginning at 17. -/
theorem tail_square_term {x : ℝ} (hx : 1<x) :
    1/x^2 ≤ 1/(x-1)-1/x := by
  rw [div_sub_div _ _ (by linarith : x-1 ≠ 0) (by linarith : x ≠ 0)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem tail_cube_term {x : ℝ} (hx : 1 < x) :
    1/x^3 ≤ 1/(2*(x-1)^2)-1/(2*x^2) := by
  rw [div_sub_div _ _ (by positivity : 2*(x-1)^2 ≠ 0)
    (by positivity : 2*x^2 ≠ 0)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h1 : 0 ≤ x^2*(3*x-2) := mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith only [h1]

theorem tail_period_square {u : ℝ} (hu : 0 ≤ u) (N : ℕ) :
    (∑ k ∈ Finset.Ico 17 N, 1/((k : ℝ)+u)^2) ≤ 1/(16+u) := by
  by_cases hN : 17 ≤ N
  · have htel : (∑ k ∈ Finset.Ico 17 N,
        (1/((k : ℝ)+u-1)-1/((k : ℝ)+u))) =
        1/(16+u)-1/((N : ℝ)+u-1) := by
      induction N,hN using Nat.le_induction with
      | base => simp <;> ring
      | succ N hN ih => rw [Finset.sum_Ico_succ_top hN,ih]; push_cast; ring
    refine (Finset.sum_le_sum (fun k hk => tail_square_term ?_)).trans ?_
    · have hk' : (17 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
      linarith
    · rw [htel]
      have hN' : (17 : ℝ) ≤ N := by exact_mod_cast hN
      have hn : 0 ≤ 1/((N : ℝ)+u-1) := div_nonneg zero_le_one (by linarith)
      linarith
  · simp [Finset.Ico_eq_empty (by omega : ¬(17 : ℕ) < N)]
    positivity

end OddZetaSix.B40a
