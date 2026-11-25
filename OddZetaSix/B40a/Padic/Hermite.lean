import OddZetaSix.B40a.Padic.JetBlock
import OddZetaSix.SixConfluentHermite

noncomputable section
open Polynomial
open scoped BigOperators

namespace OddZetaSix.B40a

/-- A change of local coordinate with a simple zero preserves vanishing of all
jets through a prescribed order. -/
theorem pow_dvd_of_comp_local {K : Type*} [Field K] (Q V : K[X])
    (hV : V.eval 0 ≠ 0) (m : ℕ)
    (h : ∀ j < m, (Q.comp (X*V)).coeff j = 0) : X^m ∣ Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨S, hS⟩ := ih (fun j hj => h j (by omega))
    have hc := h m (by omega : m < m+1)
    rw [hS,mul_comp,pow_comp,X_comp,mul_pow,mul_assoc,coeff_X_pow_mul'] at hc
    simp only [le_refl, ite_true, Nat.sub_self, coeff_zero_eq_eval_zero,
      eval_mul,eval_pow,eval_comp,eval_X,zero_mul] at hc
    have hs : S.eval 0 = 0 :=
      (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ hV)
    have hd : X^1 ∣ S := by
      apply X_pow_dvd_iff.mpr
      intro j hj
      have hj0 : j=0 := by omega
      simpa [hj0,coeff_zero_eq_eval_zero] using hs
    obtain ⟨T,hT⟩ := hd
    refine ⟨T,?_⟩
    rw [hS,hT,pow_one,pow_succ X m,mul_assoc]

/-- Transfer Taylor divisibility through squaring at a nonzero node. -/
theorem pow_dvd_of_square_jets {K : Type*} [Field K] (P : K[X]) {x : K}
    (hx : 2*x ≠ 0) (m : ℕ)
    (h : ∀ j<m, (taylor x (P.comp (X^2))).coeff j = 0) :
    (X-C (x^2))^m ∣ P := by
  let V : K[X] := X+C (2*x)
  let Q := taylor (x^2) P
  have hV : V.eval 0 ≠ 0 := by simpa [V] using hx
  have hcomp : Q.comp (X*V) = taylor x (P.comp (X^2)) := by
    simp only [Q,taylor_apply,comp_assoc,add_comp,X_comp,C_comp,pow_comp]
    congr 1
    simp only [V,map_mul,map_ofNat,map_pow]
    ring
  have hd := pow_dvd_of_comp_local Q V hV m (fun j hj => hcomp ▸ h j hj)
  have htranslate : Q.comp (X-C (x^2)) = P := by
    simp [Q,taylor_apply,comp_assoc,add_comp,X_comp,C_comp]
  obtain ⟨S,hS⟩ := hd
  refine ⟨S.comp (X-C (x^2)),?_⟩
  rw [← htranslate,hS,mul_comp,pow_comp,X_comp]

def primeIndex (n : ℕ) : ℕ := 51*n+1

def absNode (n : ℕ) (t : Fin (8*n)) : ℕ := 17*n+1+t.val

def squareNode (n : ℕ) (t : Fin (8*n)) : ZMod (primeIndex n) :=
  (absNode n t : ZMod (primeIndex n))^2

theorem squareNode_injective (n : ℕ) [Fact (primeIndex n).Prime] :
    Function.Injective (squareNode n) := by
  have hn : 0<n := by
    have hp := (Fact.out : (primeIndex n).Prime).two_le
    unfold primeIndex at hp
    omega
  intro x y h
  unfold squareNode at h
  have hx : absNode n x < primeIndex n := by
    have := x.isLt
    unfold absNode primeIndex
    omega
  have hy : absNode n y < primeIndex n := by
    have := y.isLt
    unfold absNode primeIndex
    omega
  have hsum : absNode n x + absNode n y < primeIndex n := by
    have := x.isLt
    have := y.isLt
    unfold absNode primeIndex
    omega
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with heq | hneg
  · have hv := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt hx,ZMod.val_natCast_of_lt hy] at hv
    apply Fin.ext
    unfold absNode at hv
    omega
  · have hz : ((absNode n x + absNode n y : ℕ) : ZMod (primeIndex n)) = 0 := by
      rw [Nat.cast_add,hneg,neg_add_cancel]
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hsum,ZMod.val_zero] at hv
    unfold absNode at hv
    omega

theorem two_mul_node_ne_zero (n : ℕ) [Fact (primeIndex n).Prime] (t : Fin (8*n)) :
    2 * (absNode n t : ZMod (primeIndex n)) ≠ 0 := by
  have hlt : 2*absNode n t < primeIndex n := by
    have := t.isLt
    unfold absNode primeIndex
    omega
  have hpos : 0 < 2*absNode n t := by unfold absNode; omega
  intro hz
  have hz' : ((2*absNode n t : ℕ) : ZMod (primeIndex n)) = 0 := by
    exact_mod_cast hz
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) ((ZMod.natCast_eq_zero_iff _ _).mp hz')

/-- Full five-jet injectivity on polynomials of degree less than the B40a rank.
Positive nodes are used here. Reflection changes each jet by its parity sign. -/
theorem poly_zero_of_five_jets (n : ℕ) [Fact (primeIndex n).Prime]
    (P : (ZMod (primeIndex n))[X]) (hdeg : P.natDegree < 40*n)
    (h : ∀ t : Fin (8*n), ∀ j<5,
      (taylor (absNode n t : ZMod (primeIndex n)) (P.comp (X^2))).coeff j = 0) :
    P = 0 := by
  by_contra hP
  have hcop : Set.Pairwise ((Finset.univ : Finset (Fin (8*n))) : Set (Fin (8*n)))
    (fun x y => IsCoprime ((X-C (squareNode n x))^5) ((X-C (squareNode n y))^5)) := by
    intro x _ y _ hxy
    exact (Polynomial.pairwise_coprime_X_sub_C (squareNode_injective n) hxy).pow
  have hd : (∏ t : Fin (8*n), (X-C (squareNode n t))^5) ∣ P := by
    apply Finset.prod_dvd_of_coprime hcop
    intro t _
    exact pow_dvd_of_square_jets P (two_mul_node_ne_zero n t) 5 (h t)
  have hdeg' : (∏ t : Fin (8*n), (X-C (squareNode n t))^5).natDegree = 40*n := by
    rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow 5)]
    simp_rw [(monic_X_sub_C _).natDegree_pow,natDegree_X_sub_C,mul_one]
    simp
    ring
  have hh := Polynomial.natDegree_le_of_dvd hd hP
  omega

end OddZetaSix.B40a
