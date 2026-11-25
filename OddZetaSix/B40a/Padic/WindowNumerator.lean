import OddZetaSix.B40a.Padic.Window

/-! At the auxiliary window, neither rising factorial has a vanishing
factor modulo the auxiliary prime. The pole order stays six. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

private def IsPUnit (p : ℕ) (x : ℚ) : Prop := x ≠ 0 ∧ padicValRat p x = 0

private theorem isPUnit_mul (p : ℕ) [Fact p.Prime] {x y : ℚ}
    (hx : IsPUnit p x) (hy : IsPUnit p y) : IsPUnit p (x*y) :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [padicValRat.mul hx.1 hy.1,hx.2,hy.2,add_zero]⟩

private theorem isPUnit_pow (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : IsPUnit p x) (a : ℕ) : IsPUnit p (x^a) :=
  ⟨pow_ne_zero _ hx.1, by rw [padicValRat.pow,hx.2,mul_zero]⟩

private theorem isPUnit_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IsPUnit p (f i)) : IsPUnit p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsPUnit]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isPUnit_mul p (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

private theorem isPUnit_of_nat (p m : ℕ) [Fact p.Prime] (hm : 0<m) (hd : ¬ p ∣ m) :
    IsPUnit p (m : ℚ) := by
  refine ⟨by positivity, ?_⟩
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
  rfl

private theorem isPUnit_neg (p : ℕ) {x : ℚ} (h : IsPUnit p x) : IsPUnit p (-x) :=
  ⟨neg_ne_zero.mpr h.1, by simpa using h.2⟩

private theorem not_dvd_between (p m : ℕ) (h1 : p<m) (h2 : m<2*p) : ¬ p ∣ m := by
  rintro ⟨b,rfl⟩
  have hb : 2 ≤ b := by
    by_contra! h
    interval_cases b <;> simp at h1
  nlinarith

private theorem normalization_gate_unit (n : ℕ) [Fact (primeIndex n).Prime] :
    IsPUnit (primeIndex n) (normalization n) := by
  let p := primeIndex n
  have hp : p.Prime := Fact.out
  have hn : n ≠ 0 := by
    intro hn
    exact hp.ne_one (by simp [p,primeIndex,hn])
  have ht : 2 < p := by dsimp [p,primeIndex]; omega
  have hf (m : ℕ) (hm : m < p) : IsPUnit p ((m.factorial : ℕ) : ℚ) :=
    ⟨by positivity, six_factorial_padicValRat_zero m p hp hm⟩
  have ha : IsPUnit p (2*(∏ b : Fin 12, (((50-2*offsets b)*n).factorial : ℚ))) := by
    apply isPUnit_mul p
    · exact isPUnit_of_nat p 2 (by decide) (Nat.not_dvd_of_pos_of_lt (by decide) ht)
    · apply isPUnit_prod
      intro b _
      apply hf
      exact lt_of_le_of_lt (Nat.mul_le_mul_right n (Nat.sub_le _ _)) (by unfold p primeIndex; omega)
  have hb := isPUnit_pow p (hf (25*n) (by unfold p primeIndex; omega)) 10
  unfold normalization
  exact ⟨div_ne_zero ha.1 hb.1, by rw [padicValRat.div ha.1 hb.1,ha.2,hb.2,sub_self]⟩

theorem window_numerator_unit (n k : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    let a := (taylor (-(k : ℚ)) (C (normalization n) * numerator n)).coeff 0
    a ≠ 0 ∧ padicValRat (primeIndex n) a = 0 := by
  have hh := mem_Icc.mp hk
  let p := primeIndex n
  change IsPUnit p _
  rw [taylor_coeff_zero]
  simp only [numerator,eval_mul,eval_add,eval_C,eval_X,eval_pow]
  apply isPUnit_mul p (normalization_gate_unit n)
  apply isPUnit_mul p
  · have hc : center n ≤ k := by unfold center; omega
    rw [add_comm,← sub_eq_add_neg,← neg_sub,← Nat.cast_sub hc]
    exact isPUnit_neg p (isPUnit_of_nat p _ (by unfold center; omega)
      (Nat.not_dvd_of_pos_of_lt (by unfold center; omega) (by unfold center p primeIndex; omega)))
  · apply isPUnit_pow p
    apply isPUnit_mul p
    · rw [rising,eval_prod]
      apply isPUnit_prod p
      intro j hj
      have hj' := mem_range.mp hj
      simp only [eval_add,eval_X,eval_C]
      have hle : j+1 ≤ k := by omega
      have hr : -(k : ℚ) + (1+(j : ℚ)) = -((k-(j+1) : ℕ) : ℚ) := by
        rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
        ring
      rw [hr]
      exact isPUnit_neg p (isPUnit_of_nat p _ (by omega)
        (not_dvd_between p _ (by unfold p primeIndex; omega) (by unfold p primeIndex; omega)))
    · rw [rising,eval_prod]
      apply isPUnit_prod p
      intro j hj
      have hj' := mem_range.mp hj
      simp only [eval_add,eval_X,eval_C]
      have hle : k ≤ 93*n+2+j := by omega
      have hr : -(k : ℚ)+(93*(n : ℚ)+2+(j : ℚ)) = ((93*n+2+j-k : ℕ) : ℚ) := by
        rw [Nat.cast_sub hle]
        push_cast
        ring
      rw [hr]
      exact isPUnit_of_nat p _ (by omega)
        (Nat.not_dvd_of_pos_of_lt (by omega) (by unfold p primeIndex; omega))

end OddZetaSix.B40a
