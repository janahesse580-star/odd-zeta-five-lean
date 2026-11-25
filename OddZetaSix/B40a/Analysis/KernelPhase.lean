import OddZetaSix.B40a.Analysis.Coordinates
import OddZetaSix.B40a.Analysis.RisingInventory
noncomputable section
namespace OddZetaSix.B40a.Cert
open Real

private theorem step_error {m : ℕ} {D θ η : ℝ} (hD : 0<D) (hm : (m:ℝ)≤D)
    (ht : 0≤θ) (ht' : θ≤3/D) (hη : 0<η) :
    m*((|θ|+1/D)/η)≤4/η := by
  rw [abs_of_nonneg ht]
  have H := mul_le_mul hm (add_le_add (le_refl (1/D)) ht') (by positivity) hD.le
  rw [mul_div_assoc' ,div_le_div_iff_of_pos_right hη]
  calc (m:ℝ)*(θ+1/D) ≤ D*(1/D+3/D) := by simpa [add_comm] using H
       _ = _ := by field_simp <;> norm_num

private theorem plus_bound {m : ℕ} (q : ℚ) (z : ℂ) (D a y θ w η : ℝ) (hD : 0<D)
    (hy : 0≤y) (hw : 0<w) (hwm : w≤1) (hm : (m:ℝ)=D*w)
    (ht : 0≤θ) (ht' : θ≤3/D) (hη : 0<η) (hr : z.re+(q:ℝ)=D*(a+θ)) (hi : |z.im|=D*y) :
    riseRatio m q z ≤ Real.exp (D*blockField a y w+D*Real.pi*η+4/η) := by
  rw [rise_eq m q z D a y θ hD hr hi]
  apply (normalized_upper m D a y θ w η hD hy hw hm hη).trans
  rw [Real.exp_le_exp]; have he := step_error (m:=m) hD (hm.trans_le (mul_le_of_le_one_right hD.le hwm)) ht ht' hη
  linarith only [he]

private theorem minus_bound {m : ℕ} (q : ℚ) (z : ℂ) (D a y θ w : ℝ) (hD : 2≤D)
    (hy : 0≤y) (hw : 0<w) (hwm : w≤1) (hm : (m:ℝ)=D*w)
    (ht : 0≤θ) (ht' : θ≤3/D) (ha : 1/2≤a)
    (hr : z.re+(q:ℝ)=D*(a+θ)) (hi : |z.im|=D*y) :
    poleRatio m q z ≤ Real.exp (-D*blockField a y w+9+Real.log D) := by
  have hpos : 0<D := by linarith
  have hmpos : (0:ℝ)<m := hm ▸ mul_pos hpos hw
  have hmle := hm.trans_le (mul_le_of_le_one_right hpos.le hwm)
  have hs : 1/2≤a+θ := by linarith
  have H : 1≤z.re+(q:ℝ)+m := by
    rw [hr]; nlinarith only [mul_le_mul hD hs (by norm_num) hpos.le,hmpos]
  apply (pole_le m q z D a y θ hpos hr hi H).trans
  apply (normalized_inverse m D a y θ w (1/2) hpos hy hw hm (by norm_num) ha hs).trans
  rw [Real.exp_le_exp]
  have he := step_error (m:=m) hpos hmle ht ht' (by norm_num : (0:ℝ)<1/2)
  linarith only [he,Real.log_le_log hmpos hmle]

private theorem field_decomp (x y : ℝ) :
    phaseReal x y= -2*y*Real.pi+5*(blockField (x-118/100) y (1/2)+blockField (x+68/100) y (1/2))-
    6*blockField (x-1/2) y 1-4*blockField (x-34/100) y (68/100)-2*blockField (x-32/100) y (64/100) := by
  simp only [phaseReal,phaseBlocks,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,termReal,blockField]
  norm_num
  ring_nf

def blockError (D η : ℝ) := 10*D*Real.pi*η+40/η+12*(9+Real.log D)

/-- All five families of factors of the actual complex matrix kernel are
bounded simultaneously, at every finite order and every height. -/
theorem base_phase_bound {n : ℕ} (hn : 0<n) {z : ℂ} {x y θ : ℝ} (h : Coordinates n z x y θ)
    {η : ℝ} (hη : 0<η) :
    ‖entryComplex n 0 0 z‖ ≤ 2*‖z+(OddZetaSix.B40a.center n:ℂ)‖*
      Real.exp (scaleN n*(phaseReal x y+2*y*Real.pi)+blockError (scaleN n) η) := by
  let D := scaleN n
  have N : (1:ℝ)≤n := by exact_mod_cast hn
  have hd : 2≤D := by dsimp [D,scaleN]; linarith
  have hd0 : 0<D := by linarith
  have ht : θ≤3/D := h.drift_high.trans (by gcongr <;> norm_num)
  have h2 : θ+1/D≤3/D := (add_le_add h.drift_high (le_refl (1/D))).trans_eq (by change 2/D+1/D=3/D; ring)
  have A := plus_bound (m:=25*n) 1 z D (x-118/100) y θ (1/2) η hd0 h.y_nonneg
    (by norm_num) (by norm_num) (by dsimp [D,scaleN]; push_cast; ring) h.drift_low ht hη (by simpa using h.real_eq) h.imag_eq
  have B := plus_bound (m:=25*n) (93*(n:ℚ)+2) z D (x+68/100) y (θ+1/D) (1/2) η hd0 h.y_nonneg
    (by norm_num) (by norm_num) (by dsimp [D,scaleN]; push_cast; ring) (add_nonneg h.drift_low (by positivity)) h2 hη (by
      push_cast; have E := h.real_eq; change _=D*_ at E
      rw [show D*(x+68/100+(θ+1/D))=D*(x-118/100+θ)+93*n+1 by dsimp [D,scaleN]; field_simp; ring]
      linarith only [E]) h.imag_eq
  have C := minus_bound (m:=50*n) (34*(n:ℚ)+1) z D (x-1/2) y θ 1 hd h.y_nonneg (by norm_num)
    (by norm_num) (by dsimp [D,scaleN]; push_cast; ring) h.drift_low ht (by linarith [h.x_low])
    (by push_cast; dsimp [D,scaleN]; have H := h.real_eq; unfold scaleN at H; linear_combination H) h.imag_eq
  have E := minus_bound (m:=34*n) (42*(n:ℚ)+1) z D (x-34/100) y θ (68/100) hd h.y_nonneg (by norm_num)
    (by norm_num) (by dsimp [D,scaleN]; push_cast; ring) h.drift_low ht (by linarith [h.x_low])
    (by push_cast; dsimp [D,scaleN]; have H := h.real_eq; unfold scaleN at H; linear_combination H) h.imag_eq
  have F := minus_bound (m:=32*n) (43*(n:ℚ)+1) z D (x-32/100) y θ (64/100) hd h.y_nonneg (by norm_num)
    (by norm_num) (by dsimp [D,scaleN]; push_cast; ring) h.drift_low ht (by linarith [h.x_low])
    (by push_cast; dsimp [D,scaleN]; have H := h.real_eq; unfold scaleN at H; linear_combination H) h.imag_eq
  rw [base_norm_inventory]
  let J := 2*‖z+(OddZetaSix.B40a.center n:ℂ)‖
  have posJ : 0≤J := by dsimp [J]; positivity
  have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (rise_nonneg _ _ _) (rise_nonneg _ _ _))
    (mul_le_mul A B (rise_nonneg _ _ _) (Real.exp_pos _).le) 5) posJ
  have C' := pow_le_pow_left₀ (pole_nonneg _ _ _) C 6
  have E' := pow_le_pow_left₀ (pole_nonneg _ _ _) E 4
  have F' := pow_le_pow_left₀ (pole_nonneg _ _ _) F 2
  apply (mul_le_mul (mul_le_mul (mul_le_mul H C' (pow_nonneg (pole_nonneg _ _ _) _) (by positivity)) E'
    (pow_nonneg (pole_nonneg _ _ _) _) (by positivity)) F' (pow_nonneg (pole_nonneg _ _ _) _) (by positivity)).trans_eq
  simp only [←Real.exp_add,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
  rw [←mul_assoc 2 ‖z+(OddZetaSix.B40a.center n:ℂ)‖] 
  change J*_ = J*_
  congr 1
  rw [field_decomp]; unfold blockError; change _ = Real.exp (D*_+_)
  congr 1; push_cast; ring
end OddZetaSix.B40a.Cert
