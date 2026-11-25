import OddZetaSix.B40a.Analysis.WitnessBudget
import OddZetaSix.B40a.Analysis.PhaseEndpoints

noncomputable section
namespace OddZetaSix.B40a.Witness
open Real Cert Finset
def squarePoint (x y : ℚ) : ℂ := ((x:ℂ)+(y:ℂ)*Complex.I)^2
def endCode (t : ℤ) (c : Cert.Circle) :=
  let z := contourZ t
  max (c.radius^2) (maxDistSq (squareBox z.1 z.2) c.re c.im)

def boxOK (b : Box) : Prop := -50000000≤b.xlo ∧ b.xlo≤50000000 ∧
  -50000000≤b.xhi ∧ b.xhi≤50000000 ∧ -50000000≤b.ylo ∧ b.ylo≤50000000 ∧
  -50000000≤b.yhi ∧ b.yhi≤50000000
instance (b : Box) : Decidable (boxOK b) := by unfold boxOK; infer_instance

private theorem dim_bound (x : ℚ) (c : ℤ) :
    |(coord:ℝ)*x-c| ≤ (max ((qfloor (coord*x)-c).natAbs) ((qceil (coord*x)-c).natAbs):ℕ) := by
  have l := floor_bound ((coord:ℚ)*x); have h := ceil_bound ((coord:ℚ)*x)
  push_cast at l h
  rw [Nat.cast_max]
  have eqA (z : ℤ) : ((z-c).natAbs:ℝ)=|(z:ℝ)-c| := by
    rw [←Int.cast_sub,←Int.cast_abs,←Int.natCast_natAbs]; simp
  rw [eqA,eqA]
  apply abs_le.mpr
  constructor
  · have L := le_max_left |((qfloor (coord*x):ℤ):ℝ)-c| |((qceil (coord*x):ℤ):ℝ)-c|
    linarith only [l,L,neg_abs_le (((qfloor (coord*x):ℤ):ℝ)-c)]
  · have U := le_max_right |((qfloor (coord*x):ℤ):ℝ)-c| |((qceil (coord*x):ℤ):ℝ)-c|
    linarith only [h,U,le_abs_self (((qceil (coord*x):ℤ):ℝ)-c)]

private theorem dist_upper (x y : ℚ) (i : Index) :
    ‖squarePoint x y-u i‖^2 ≤ ((maxDistSq (squareBox x y) (entry i).re (entry i).im:ℤ):ℝ)/(coord:ℝ)^2 := by
  let X := x*x-y*y; let Y := 2*x*y
  let c := entry i
  have hx := dim_bound X c.re; have hy := dim_bound Y c.im
  have sx := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have sy := pow_le_pow_left₀ (abs_nonneg _) hy 2
  rw [sq_abs] at sx sy
  have hc : (0:ℝ)<coord := by norm_num [coord]
  rw [le_div_iff₀ (sq_pos_of_pos hc)]
  have eq : ‖squarePoint x y-u i‖^2*(coord:ℝ)^2=
      ((coord:ℝ)*X-c.re)^2+((coord:ℝ)*Y-c.im)^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp [squarePoint,u,c,X,Y,Complex.sub_re,Complex.sub_im,pow_two,Complex.mul_re,Complex.mul_im,coord]
    <;> ring
  rw [eq]
  simpa only [maxDistSq,squareBox,rect,X,Y,c,Int.cast_add,Int.cast_pow,Int.cast_max,Int.cast_natCast,Nat.cast_max] using add_le_add sx sy

private theorem end_range (t : ℤ) (i : Index) (h : boxOK (squareBox (contourZ t).1 (contourZ t).2)) :
    0<endCode t (entry i) ∧ (endCode t (entry i)).toNat.log2<80 := by
  let c := entry i
  let B := squareBox (contourZ t).1 (contourZ t).2
  have H := ranges i
  have bound (m a : ℤ) (hm : -50000000≤m ∧ m≤50000000) (ha : -3000000≤a ∧ a≤3000000) :
      (m-a).natAbs≤53000000 := by omega
  have X := max_le (bound B.xlo c.re ⟨h.1,h.2.1⟩ ⟨H.1,H.2.1⟩)
    (bound B.xhi c.re ⟨h.2.2.1,h.2.2.2.1⟩ ⟨H.1,H.2.1⟩)
  have Y := max_le (bound B.ylo c.im ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩ ⟨H.2.2.1,H.2.2.2.1⟩)
    (bound B.yhi c.im ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩ ⟨H.2.2.1,H.2.2.2.1⟩)
  have b : maxDistSq B c.re c.im ≤ 5620000000000000 := by
    unfold maxDistSq
    have xx := Nat.pow_le_pow_left X 2; have yy := Nat.pow_le_pow_left Y 2
    norm_num at xx yy; exact_mod_cast (show _+_≤5620000000000000 by omega)
  have rad := pow_le_pow_left₀ H.2.2.2.2.1.le H.2.2.2.2.2 2
  have T : 0<endCode t c ∧ endCode t c≤5620000000000000 :=
    ⟨(sq_pos_of_pos H.2.2.2.2.1).trans_le (le_max_left _ _),max_le (by change (entry i).radius^2≤5620000000000000; norm_num at rad; omega) b⟩
  exact ⟨T.1,(Nat.log2_lt (n:=(endCode t c).toNat) (by omega)).mpr (by norm_num; omega)⟩

private theorem radius_envelope (t : ℤ) (i : Index)
    (hb : boxOK (squareBox (contourZ t).1 (contourZ t).2)) :
    2*(fix:ℝ)*circlePotential (u i) (r i) (squarePoint (contourZ t).1 (contourZ t).2) ≤
      squaredLog lookup (endCode t (entry i)) true := by
  have ht := end_range t i hb
  have U := (squaredLog_sound lookup lookup_ok _ ht.1 ht.2).2
  let c := entry i
  let z := squarePoint (contourZ t).1 (contourZ t).2
  let D := endCode t c
  have cc : (0:ℝ)<coord := by norm_num [coord]
  have hdiv := fun {a b : ℤ} (h : a≤b)=>div_le_div_of_nonneg_right
      ((Int.cast_le (R:=ℝ)).mpr h) (sq_nonneg (coord:ℝ))
  have hrad : (r i)^2 ≤ (D:ℝ)/(coord:ℝ)^2 := by
    have HH := hdiv (le_max_left (c.radius^2) (maxDistSq (squareBox (contourZ t).1 (contourZ t).2) c.re c.im))
    rw [Int.cast_pow] at HH; exact (div_pow _ _ _).le.trans HH
  have hd : ‖z-u i‖^2 ≤ (D:ℝ)/(coord:ℝ)^2 :=
    (dist_upper _ _ _).trans (hdiv (le_max_right _ _))
  have hp : 0<max (r i) ‖z-u i‖ := (valid i).1.trans_le (le_max_left _ _)
  have hs : (max (r i) ‖z-u i‖)^2 ≤ (D:ℝ)/(coord:ℝ)^2 := by
    rcases le_total (r i) ‖z-u i‖ with h|h
    · simpa [max_eq_right h] using hd
    · simpa [max_eq_left h] using hrad
  have H := Real.log_le_log (sq_pos_of_pos hp) hs
  rw [Real.log_pow] at H
  change 2*(fix:ℝ)*Real.log (max (r i) ‖z-u i‖)≤_
  apply le_trans _ U
  linarith only [mul_le_mul_of_nonneg_left H (by norm_num [fix] : (0:ℝ)≤fix)]

theorem endpoint_sound (t : ℤ) (hb : boxOK (squareBox (contourZ t).1 (contourZ t).2)) :
    (fix:ℝ)*(phaseReal (contourZ t).1 (contourZ t).2+
      (8/5)*potential (squarePoint (contourZ t).1 (contourZ t).2)) ≤ endpoint lookup circles t := by
  let z := squarePoint (contourZ t).1 (contourZ t).2
  let cost := fun c=>c.mass*squaredLog lookup (endCode t c) true
  have sumEq : (∑ i : Index,cost (entry i))=(entries.map cost).sum := sum_entries cost
  let m := (entries.map cost).sum
  have qr : (2*(m:ℝ))/(5*massTotal)≤(iceil (2*m) (5*massTotal):ℝ) := by
    have H := Int.ediv_mul_le (-(2*m)) (by norm_num [massTotal] : (5*massTotal:ℤ)≠0)
    apply (div_le_iff₀ (by norm_num [massTotal] : (0:ℝ)<5*massTotal)).mpr
    unfold iceil; push_cast; exact_mod_cast (show 2*m≤ -(-(2*m)/(5*massTotal))*(5*massTotal) by linarith only [H])
  have hl := sum_le_sum (s:=univ) (fun i _=>mul_le_mul_of_nonneg_left (radius_envelope t i hb) (valid i).2)
  have hphase := phaseUpper_sound t
  change _≤((phaseUpper t+iceil (2*m) (5*massTotal):ℤ):ℝ)
  have Q : (∑ i,b i*(squaredLog lookup (endCode t (entry i)) true:ℝ))=(m:ℝ)/(2*massTotal) := by
    rw [show m=∑ i,cost (entry i) from sumEq.symm]
    push_cast; rw [Finset.sum_div]; apply sum_congr rfl; intro i _
    unfold cost b; push_cast; ring
  rw [Q] at hl
  have factor : (∑ i,b i*(2*(fix:ℝ)*circlePotential (u i) (r i) z))=2*fix*potential z := by
    unfold potential; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  rw [factor] at hl
  change (fix:ℝ)*(_+(8/5)*potential z)≤_
  push_cast; norm_num [massTotal] at hl qr ⊢
  linarith only [hl,qr,hphase]

end OddZetaSix.B40a.Witness
