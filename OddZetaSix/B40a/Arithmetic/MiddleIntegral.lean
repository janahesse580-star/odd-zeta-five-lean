import OddZetaSix.B40a.Arithmetic.MiddleRowExpression

noncomputable section
namespace OddZetaSix.B40a.Cert.Transport
open Set Finset Sweep
attribute [local irreducible] middleRows

def scaleOf (x : ℚ) (hx : 0<x) : Scale := ⟨x.num,x.den,Rat.num_pos.mpr hx,by exact_mod_cast x.den_pos⟩
theorem scaleOf_ratio (x : ℚ) (hx : 0<x) : (scaleOf x hx).ratio=(x:ℝ) := by
  simp [scaleOf,Scale.ratio,Rat.cast_def]

theorem real_row_eval {r : ArithRow} (hr : r∈middleRows) {s : Scale}
    (hs : s.ratio∈Ioo (r.left:ℝ) r.right) (x : ℚ) (hx : 0<x)
    (ht : (x:ℝ)∈Ioo (r.left:ℝ) r.right) :
    (rowExpr s).eval x = 2000*(middleValue x:ℝ) := by
  let t := scaleOf x hx
  have hrt : t.ratio=(x:ℝ) := scaleOf_ratio _ _
  have H := raw_row_eval hr hs (hrt ▸ ht : t.ratio∈_)
  dsimp only at H
  rw [hrt] at H
  rw [middleValue_eq_best]
  change _ = 2000*((((best _ (4*t.p) (4*t.d) (rowK t) (rowK t+1):ℤ):ℚ)/(2000*(4*t.d):ℤ):ℚ):ℝ)
  push_cast
  change _=2000*(((best (middleClasses (4*t.p) (4*t.d)) (4*t.p) (4*t.d) (rowK t) (rowK t+1):ℤ):ℝ)/(2000*(4*(t.d:ℝ))))
  rw [H]
  have hd : (t.d:ℝ)≠0 := by exact_mod_cast t.hd.ne'
  field_simp
  <;> ring

theorem charge_nonneg (t : Scale) (q : ℕ) (hq : q≤rowK t) :
    0≤rowCharge (4*t.p) (4*t.d) (rowK t) q := by
  let K := rowK t
  have hp : 0<4*t.p := by have := t.hp; omega
  have hd : 0≤80*(4*t.d) := by have := t.hd; omega
  have hk : (K:ℤ)*(4*t.p)≤80*(4*t.d) := by
    dsimp [K,rowK]
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hd hp.le)]
    exact Int.ediv_mul_le _ (by omega)
  have hi : (K+q+1)*(K-q)/2≤K*(K-q) := by
    by_cases he : K=q
    · simp [he]
    · have : K+q+1≤2*K := by change q≤K at hq; omega
      have H := Nat.mul_le_mul_right (K-q) this
      rw [mul_assoc] at H
      omega
  have hiZ : (((K+q+1)*(K-q)/2:ℕ):ℤ)≤(K:ℤ)*((K-q:ℕ):ℤ) := by exact_mod_cast hi
  change 0≤80*(4*t.d)*((K-q:ℕ):ℤ)-(4*t.p)*_
  have h1 := mul_le_mul_of_nonneg_left hiZ hp.le
  have h2 := mul_le_mul_of_nonneg_right hk (show (0:ℤ)≤((K-q:ℕ):ℤ) by positivity)
  rw [mul_comm (K:ℤ),mul_assoc] at h2
  exact sub_nonneg.mpr (h1.trans h2)

theorem best_nonneg (t : Scale) :
    0 ≤ best (middleClasses (4*t.p) (4*t.d)) (4*t.p) (4*t.d) (rowK t) (rowK t+1) := by
  let bs := middleClasses (4*t.p) (4*t.d)
  apply le_best_of_all_rows _ _ _ _ _ (valid_classes t)
  intro q hq
  apply add_nonneg (charge_nonneg t q hq)
  rw [book_cap]
  apply sum_nonneg; intro j hj
  apply le_min (by have := t.hd; omega)
  rw [folded_population _ _ _ (mem_Ico.mp hj).1 (fun b h=>(valid_classes t b h).2)]
  apply List.sum_nonneg
  intro z hz
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
  apply mul_nonneg (valid_classes t _ hb).1
  apply sum_nonneg; intro i _
  unfold eligible; split <;> decide

theorem row_sides {r : ArithRow} (hr : r∈middleRows) : 0<r.left ∧ r.left<r.right := by
  have H := List.all_eq_true.mp middleRows_freq r hr
  simp only [checkMiddleFrequencies,Bool.and_eq_true,decide_eq_true_eq] at H
  exact H.1

def midpoint (r : ArithRow) : ℚ := (r.left+r.right)/2
theorem mid_in {r : ArithRow} (hr : r∈middleRows) : 0<midpoint r ∧
    (midpoint r:ℝ) ∈ Ioo (r.left:ℝ) r.right := by
  obtain ⟨ha,hb⟩ := row_sides hr
  have hm : r.left<midpoint r ∧ midpoint r<r.right := by unfold midpoint; constructor <;> linarith
  exact ⟨ha.trans hm.1,by exact_mod_cast hm.1,by exact_mod_cast hm.2⟩

def model (r : ArithRow) (hr : r∈middleRows) := rowExpr (scaleOf (midpoint r) (mid_in hr).1)
theorem model_at {r : ArithRow} (hr : r∈middleRows) (x : ℚ) (hx : (x:ℝ)∈Ioo (r.left:ℝ) r.right) :
    (model r hr).eval x=2000*(middleValue x:ℝ) := by
  apply real_row_eval hr _ _ _ hx
  · simpa only [scaleOf_ratio] using (mid_in hr).2
  · exact_mod_cast (show (0:ℝ)<x from (by exact_mod_cast (row_sides hr).1 : (0:ℝ)<r.left).trans hx.1)

theorem model_nonneg {r : ArithRow} (hr : r∈middleRows) :
    ∀ x∈Icc (r.left:ℝ) r.right,0≤(model r hr).eval x := by
  let S : Set ℝ := {x | 0≤(model r hr).eval x}
  have hS : IsClosed S := isClosed_le continuous_const (model r hr).eval_continuous
  let I := Ioo (r.left:ℝ) r.right
  have hpart : I ∩ Set.range ((↑):ℚ→ℝ) ⊆ S := by
    rintro _ ⟨hi,⟨x,rfl⟩⟩
    have hx : 0<x := by exact_mod_cast (show (0:ℝ)<x from (by exact_mod_cast (row_sides hr).1 : (0:ℝ)<r.left).trans hi.1)
    let t := scaleOf x hx
    have hrt : t.ratio=(x:ℝ) := scaleOf_ratio _ _
    let m := scaleOf (midpoint r) (mid_in hr).1
    have hm : m.ratio∈I := by simpa only [m,scaleOf_ratio] using (mid_in hr).2
    have H := raw_row_eval hr hm (hrt ▸ hi : t.ratio∈I)
    have Hpos : 0≤(4*(t.d:ℝ))*(rowExpr m).eval t.ratio := H ▸ (by exact_mod_cast best_nonneg t)
    have hd : 0<(4:ℝ)*t.d := mul_pos (by norm_num) (by exact_mod_cast t.hd)
    exact hrt ▸ (nonneg_of_mul_nonneg_right Hpos hd)
  have hop : I ⊆ S := (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal hpart hS)
  have hall := closure_minimal hop hS
  rw [show closure I=Icc (r.left:ℝ) r.right from closure_Ioo (by exact_mod_cast (row_sides hr).2.ne)] at hall
  exact fun _ h=>hall h

theorem model_integral {r : ArithRow} (hr : r∈middleRows) :
    (∫ x in (r.left:ℝ)..r.right,(model r hr).eval x)≤2000*(rowValue false r:ℝ) := by
  have h := (model r hr).integral_le_midpoint (by exact_mod_cast (row_sides hr).2.le : (r.left:ℝ)≤r.right)
  have hm : ((r.left:ℝ)+r.right)/2=(midpoint r:ℝ) := by simp [midpoint]
  rw [hm,model_at hr _ (mid_in hr).2] at h
  convert h using 1
  simp [rowValue,midpoint]
  ring
end OddZetaSix.B40a.Cert.Transport
