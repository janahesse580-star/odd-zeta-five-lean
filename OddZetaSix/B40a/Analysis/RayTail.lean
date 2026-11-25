import OddZetaSix.B40a.Analysis.PrimitiveVariation
import OddZetaSix.B40a.Analysis.CheckedEndpoints

noncomputable section
namespace OddZetaSix.B40a.Cert
open Real Set

/-- Uniform horizontal integral bound for every block on the vertical ray. -/
theorem ray_primitive_bounds {a b y : ℝ} (hy : 4≤y) (ha : 0≤a) (hab : a<b) (hb : b≤3) :
    (b-a)*Real.log y≤primReal b y-primReal a y ∧
    primReal b y-primReal a y≤(b-a)*(Real.log y+1/4) := by
  have yp : 0<y := by linarith
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (fun x=>primReal x y)
    (fun x=>Real.log (x*x+y*y)/2) hab (fun x _=>(prim_horizontal x y yp).continuousAt.continuousWithinAt)
    (fun x _=>prim_horizontal x y yp)
  have cn := ha.trans hc.1.le
  have cu := hc.2.le.trans hb
  have low := Real.log_le_log (mul_pos yp yp) (show y*y≤c*c+y*y by nlinarith [sq_nonneg c])
  have high := Real.log_le_log (add_pos_of_nonneg_of_pos (mul_self_nonneg c) (mul_pos yp yp))
    (show c*c+y*y≤(5/4*y)*(5/4*y) by nlinarith [mul_self_le_mul_self cn cu, mul_self_le_mul_self (by norm_num : (0:ℝ)≤4) hy])
  have yp' : 0<(5/4:ℝ)*y := by positivity
  rw [Real.log_mul yp.ne' yp.ne'] at low
  rw [Real.log_mul yp'.ne' yp'.ne',Real.log_mul (by norm_num) yp.ne'] at high
  have hL : Real.log (5/4:ℝ)≤1/4 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5/4)]
  rw [eq_div_iff (sub_pos.mpr hab).ne'] at he
  rw [←he]
  constructor
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by linarith) (sub_pos.mpr hab).le
  · rw [mul_comm (b-a)]; exact mul_le_mul_of_nonneg_right (by linarith) (sub_pos.mpr hab).le

private def ra (p : ℤ) : ℝ := 327/200+((p:ℝ)-118)/100
private def width (a b : ℤ) : ℝ := ((b:ℝ)-a)/100

private theorem ray_positive (a b : ℤ) (y : ℝ) (hy : 4≤y) (ha : 0≤ra a) (hb : ra b≤3)
    (hw : width a b=1/2) :
    termReal (327/200) y (a,b,5) ≤ 5*(1/2)*(Real.log y+9/4) := by
  have e : ra b-ra a=width a b := by unfold ra width; ring
  have H := (ray_primitive_bounds hy ha (by linarith only [e,hw]) hb).2
  rw [e,hw] at H
  have lg := Real.log_inv (2:ℝ)
  have l2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  change 5*((primReal (ra b) y-primReal (ra a) y)-width a b*(Real.log (width a b)-1))≤_
  rw [hw,one_div,lg]
  linarith only [H,l2]

private theorem ray_negative (a b k : ℤ) (y : ℝ) (hy : 4≤y) (ha : 0≤ra a) (hb : ra b≤3)
    (hw : 0<width a b) (hw' : width a b≤1) (hk : k≤0) :
    termReal (327/200) y (a,b,k) ≤ k*width a b*Real.log y := by
  have e : ra b-ra a=width a b := by unfold ra width; ring
  have H := (ray_primitive_bounds hy ha (by linarith only [e,hw]) hb).1
  rw [e] at H
  have L := Real.log_nonpos hw.le hw'
  have T := mul_nonpos_of_nonneg_of_nonpos hw.le (show Real.log (width a b)-1≤0 by linarith)
  change (k:ℝ)*((primReal (ra b) y-primReal (ra a) y)-width a b*(Real.log (width a b)-1))≤_
  rw [mul_assoc]
  exact mul_le_mul_of_nonpos_left (by linarith only [T,H]) (by exact_mod_cast hk)

theorem ray_phase_bound (y : ℝ) (hy : 4≤y) :
    phaseReal (327/200) y ≤ -2*y*Real.pi-5*Real.log y+45/4 := by
  have A := ray_positive 0 50 y hy (by norm_num [ra]) (by norm_num [ra]) (by norm_num [width])
  have B := ray_positive 186 236 y hy (by norm_num [ra]) (by norm_num [ra]) (by norm_num [width])
  have C := ray_negative 68 168 (-6) y hy (by norm_num [ra]) (by norm_num [ra])
    (by norm_num [width]) (by norm_num [width]) (by decide)
  have D := ray_negative 84 152 (-4) y hy (by norm_num [ra]) (by norm_num [ra])
    (by norm_num [width]) (by norm_num [width]) (by decide)
  have E := ray_negative 86 150 (-2) y hy (by norm_num [ra]) (by norm_num [ra])
    (by norm_num [width]) (by norm_num [width]) (by decide)
  norm_num only [width,Int.cast_ofNat,Int.cast_neg] at C D E
  simp only [phaseReal,phaseBlocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  linarith only [A,B,C,D,E]

end OddZetaSix.B40a.Cert

namespace OddZetaSix.B40a.Witness
open Cert Real Finset
def rayZ (y : ℝ) : ℂ := (327/200:ℝ)+(y:ℂ)*Complex.I

private theorem ray_norm (y : ℝ) : ‖rayZ y‖^2=(327/200:ℝ)^2+y^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [rayZ,pow_two]

private theorem radius_le (i : Index) : r i≤1 := by
  unfold r
  rw [div_le_one (by norm_num [coord] : (0:ℝ)<coord)]
  exact_mod_cast (ranges i).2.2.2.2.2

private theorem center_le (i : Index) : ‖u i‖≤6 := by
  have H := ranges i
  have h1 : |((entry i).re:ℝ)|≤3000000 := by exact_mod_cast abs_le.mpr ⟨H.1,H.2.1⟩
  have h2 : |((entry i).im:ℝ)|≤3000000 := by exact_mod_cast abs_le.mpr ⟨H.2.2.1,H.2.2.2.1⟩
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp [u,coord,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,abs_div]
  linarith only [h1,h2]

theorem ray_potential_bound (y : ℝ) (hy : 4≤y) :
    potential ((rayZ y)^2) ≤ 1+2*Real.log y := by
  have yp : 0<y := by linarith
  have hs : 16≤y^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤4) hy]
  have each (i : Index) : circlePotential (u i) (r i) ((rayZ y)^2)≤1+2*Real.log y := by
    have D := (norm_sub_le ((rayZ y)^2) (u i)).trans (add_le_add (le_refl _) (center_le i))
    rw [norm_pow,ray_norm] at D
    have R := radius_le i
    have UB : max (r i) ‖rayZ y^2-u i‖≤2*y^2 := max_le (by linarith) (by linarith)
    have H := Real.log_le_log ((valid i).1.trans_le (le_max_left _ _)) UB
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 yp.ne'),Real.log_pow] at H
    unfold circlePotential
    norm_num only [Nat.cast_ofNat] at H
    linarith only [H,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  calc potential ((rayZ y)^2) ≤ ∑ i,b i*(1+2*Real.log y) :=
         sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (each i) (valid i).2
       _ = _ := by rw [←sum_mul,mass,one_mul]

/-- On the entire ray the limiting combined field is strictly below the
certificate peak, with explicit linear decay in height. -/
theorem ray_field_decay (y : ℝ) (hy : 4≤y) :
    phaseReal (327/200) y+(8/5)*potential ((rayZ y)^2) ≤ (peak:ℝ)/fix-6*(y-4) := by
  have P := ray_phase_bound y hy
  have U := ray_potential_bound y hy
  have L := Real.log_nonneg (show 1≤y by linarith)
  have Y := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (show 0≤y by linarith)
  norm_num [peak,fix]
  linarith only [P,U,L,Y]
end OddZetaSix.B40a.Witness
