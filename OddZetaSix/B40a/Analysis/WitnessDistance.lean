import OddZetaSix.B40a.Analysis.WitnessEnergy
import OddZetaSix.B40a.Analysis.LogLookup

noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Orbit Real MeasureTheory

def distCode (a b : Cert.Circle) : ℤ :=
  if a.re=b.re ∧ a.im=b.im then a.radius^2 else (a.re-b.re)^2+(a.im-b.im)^2

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem lookup_ok : checkLookup lookup=true := by decide +kernel

private theorem ranges_check : entries.all (fun c=>decide (c.re.natAbs≤3000000 ∧
    c.im.natAbs≤3000000 ∧ 0<c.radius ∧ c.radius≤1000000))=true := by decide +kernel

theorem ranges (i : Index) : -3000000≤(entry i).re ∧ (entry i).re≤3000000 ∧
    -3000000≤(entry i).im ∧ (entry i).im≤3000000 ∧ 0<(entry i).radius ∧ (entry i).radius≤1000000 := by
  have H := of_decide_eq_true (List.all_eq_true.mp ranges_check _ (List.get_mem entries i))
  change (entry i).re.natAbs≤3000000 ∧ (entry i).im.natAbs≤3000000 ∧ 0<(entry i).radius ∧ (entry i).radius≤1000000 at H
  omega

private theorem code_bounds (i j : Index) :
    0<distCode (entry i) (entry j) ∧ (distCode (entry i) (entry j)).toNat.log2<80 := by
  have ha := ranges i; have hb := ranges j
  have sqBd (x : ℤ) (hl : -6000000≤x) (hh : x≤6000000) : x^2≤36000000000000 := by
    nlinarith only [mul_nonneg (show 0≤6000000-x by omega) (show 0≤6000000+x by omega)]
  let a := entry i
  let b := entry j
  have BD : 0<distCode a b ∧ distCode a b≤72000000000000 := by
    unfold distCode
    split_ifs with h
    · exact ⟨sq_pos_of_pos ha.2.2.2.2.1,(sqBd _ (by dsimp [a]; omega) (by dsimp [a]; omega)).trans (by decide)⟩
    · have eq : a.re-b.re≠0 ∨ a.im-b.im≠0 := by omega
      constructor
      · rcases eq with h|h
        · nlinarith only [sq_pos_of_ne_zero h,sq_nonneg (a.im-b.im)]
        · nlinarith only [sq_pos_of_ne_zero h,sq_nonneg (a.re-b.re)]
      · linarith only [sqBd (a.re-b.re) (by dsimp [a,b]; omega) (by dsimp [a,b]; omega),
          sqBd (a.im-b.im) (by dsimp [a,b]; omega) (by dsimp [a,b]; omega)]
  change 0<distCode a b ∧ (distCode a b).toNat.log2<80
  have nz : (distCode a b).toNat≠0 := by omega
  exact ⟨BD.1,(Nat.log2_lt nz).mpr (by norm_num; omega)⟩

theorem pair_lower (i j : Index) :
    (squaredLog lookup (distCode (entry i) (entry j)) false:ℝ)/(2*fix) ≤
      interaction (u i) (u j) (r i) (r j) := by
  have hd := code_bounds i j
  have L := (squaredLog_sound lookup lookup_ok _ hd.1 hd.2).1
  have hi := (valid i).1; have hj := (valid j).1
  have fx : (0:ℝ)<fix := by norm_num [fix]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*fix)).mpr
  apply L.trans
  apply le_trans (b:= (fix:ℝ)*(2*interaction (u i) (u j) (r i) (r j))) _ (by ring_nf; rfl)
  apply mul_le_mul_of_nonneg_left _ fx.le
  by_cases h : (entry i).re=(entry j).re ∧ (entry i).im=(entry j).im
  · have same : u i=u j := by unfold u; rw [h.1,h.2]
    have equal : interaction (u i) (u j) (r i) (r j)=Real.log (max (r j) (r i)) := by
      rw [interaction,same]; apply circleAverage_const_on_circle
      intro z hz
      have H : ‖z-u j‖=|r i| := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
      simp [circlePotential,H,abs_of_pos hi]
    have he : ((distCode (entry i) (entry j):ℤ):ℝ)/(coord:ℝ)^2=(r i)^2 := by
      simp [distCode,h,r,div_pow]
    rw [he,Real.log_pow,equal]; push_cast
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hi (le_max_right _ _)) (by norm_num)
  · have eq : ((distCode (entry i) (entry j):ℤ):ℝ)/(coord:ℝ)^2=‖u i-u j‖^2 := by
      simp only [distCode,ite_eq_right h,Int.cast_add,Int.cast_pow,Int.cast_sub,←Complex.normSq_eq_norm_sq,
        Complex.normSq_apply,Complex.sub_re,Complex.sub_im,u]
      simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,coord]; ring
    have hz : u i≠u j := by
      intro e
      have hv : (0:ℝ)<((distCode (entry i) (entry j):ℤ):ℝ)/(coord:ℝ)^2 :=
        div_pos (by exact_mod_cast hd.1) (by norm_num [coord])
      rw [eq,e,sub_self,norm_zero] at hv
      norm_num at hv
    rw [eq,Real.log_pow]; push_cast
    exact mul_le_mul_of_nonneg_left (circleInteraction_ge_log (u j) (u i) _ _ hj hi hz) (by norm_num)

end OddZetaSix.B40a.Witness
