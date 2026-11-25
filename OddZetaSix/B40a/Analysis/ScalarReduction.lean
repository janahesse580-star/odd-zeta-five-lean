import OddZetaSix.B40a.Analysis.WeightedContour
import OddZetaSix.B40a.Analysis.WitnessBudget
import OddZetaSix.B40a.Padic.ConcreteGate

noncomputable section
namespace OddZetaSix.B40a.Witness
open Filter MeasureTheory Cert Matrix
open scoped Topology

theorem numeric_gap :
    (12:ℝ)/5+8/5*Real.log (5/8)+(peak:ℝ)/fix-4/5*energy < -619/100 := by
  have he := energy_lower
  let i := plus ⟨3*fix,3*fix⟩ (scale (logRat (8/5)) (-2))
  have hbase : Encloses ⟨3*fix,3*fix⟩ 3 := by norm_num [Encloses,fix]
  have Ha := hbase.add ((logRat_sound (8/5) (by norm_num)).mul_rat (-2))
  have hN : aCert≤ (-61902/10000:ℚ) := by decide +kernel
  have hR := (Rat.cast_le (K:=ℝ)).mpr hN
  change (((4/5:ℚ)*(i.hi:ℚ)/fix+(peak:ℚ)/fix-(4/5:ℚ)*((energySum:ℚ)/(4*(massTotal:ℚ)^2*fix)):ℚ):ℝ)≤_ at hR
  have hf : (0:ℝ)<fix := by norm_num [fix]
  have hh : (fix:ℝ)*(3-2*Real.log (8/5)) ≤ (i.hi:ℝ) := by
    have H := Ha.2; push_cast at H; simpa only [neg_mul,←sub_eq_add_neg] using H
  have hl : Real.log (5/8)= -Real.log (8/5) := by
    convert Real.log_inv (8/5:ℝ) using 2 <;> norm_num
  rw [hl]; push_cast at hR
  norm_num [fix,massTotal] at hh hR he ⊢
  linarith only [hh,hR,he]

/-- The only scalar rate needed after the signed-circle comparison. Height
q goes to infinity separately for each n, matching the contour residue limit. -/
def ScalarPeak : Prop :=
  ∀ δ : ℝ,0<δ → ∀ᶠ n : ℕ in atTop,∀ᶠ q : ℕ in atTop,
    oneIntegral n q ≤ Real.exp (50*(n:ℝ)*((peak:ℝ)/fix+δ))

private theorem actual_det_of_scalar (n : ℕ) (hn : 0<n) (P : ℝ)
    (H : ∀ᶠ q : ℕ in atTop,oneIntegral n q≤Real.exp (50*(n:ℝ)*P)) :
    |(fiveFunctional n).det| ≤ basisNormalization n*
      Real.exp (correction n (1/(n:ℝ)) - (fiveRank n:ℝ)^2*energy + normalizer n*P) := by
  let ε := 1/(n:ℝ)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hq := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (bendNodeY n 7))
  have hb : ∀ᶠ q : ℕ in atTop, ((fiveRank n).factorial:ℝ)*‖(bendMatrix n q).det‖ ≤
      basisNormalization n*Real.exp (correction n ε-(fiveRank n:ℝ)^2*energy+normalizer n*P) := by
    filter_upwards [hq,H] with q hq hP
    apply (finite_det_bound n hn q hq hε).trans
    have hpos : 0≤oneIntegral n q := integral_nonneg (fun a=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    have L := pow_le_pow_left₀ hpos hP (fiveRank n)
    have B := mul_le_mul_of_nonneg_left L (mul_nonneg (basisNormalization_pos n hn).le ((show 0<pref n ε from Real.exp_pos _).le))
    apply B.trans_eq
    rw [mul_assoc,←Real.exp_nat_mul]
    unfold pref
    rw [←Real.exp_add]; congr 2
    unfold fiveRank normalizer; push_cast; ring
  have Hlim := le_of_tendsto ((det_bendMatrix_tendsto n).norm.const_mul ((fiveRank n).factorial:ℝ)) hb
  have hdet : ((fiveFunctional n).map Complex.ofReal).det=((fiveFunctional n).det:ℂ) :=
    (Complex.ofRealHom.map_det (fiveFunctional n)).symm
  rw [hdet,norm_mul,norm_pow,norm_neg,norm_mul,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at Hlim
  have htwo : ‖(2:ℂ)‖=2 := by norm_num
  rw [htwo,←mul_assoc] at Hlim
  have h1 := one_le_mul_of_one_le_of_one_le
    (show (1:ℝ)≤(fiveRank n).factorial by exact_mod_cast Nat.factorial_pos _)
    (one_le_pow₀ (by linarith [Real.pi_gt_three] : 1≤2*Real.pi) (n:=fiveRank n))
  exact (le_mul_of_one_le_left (abs_nonneg _) h1).trans Hlim

/-- Conditional reduction, not a proof of ScalarPeak. The numeric test is on
the actual witness energy and eventual determinant, not on isolated fields. -/
theorem det_exp_of_scalar_peak (H : ScalarPeak) :
    ∀ᶠ n : ℕ in atTop, |(fiveFunctional n).det| ≤ Real.exp ((-619/100:ℝ)*normalizer n) := by
  let B : ℝ := 12/5+8/5*Real.log (5/8)
  let P : ℝ := (peak:ℝ)/fix
  let δ : ℝ := (-619/100-(B+P-4/5*energy))/4
  have hp : 0<δ := by unfold δ B P; linarith only [numeric_gap]
  have hc := correction_rate.eventually_lt_const hp
  filter_upwards [H δ hp,hc,basisNormalization_eventually_le δ hp,eventually_gt_atTop (0:ℕ)]
    with n h1 h2 h3 hn
  have hN : 0<normalizer n := by unfold normalizer; positivity
  have hrel : (fiveRank n:ℝ)^2=(4/5:ℝ)*normalizer n := by unfold fiveRank normalizer; push_cast; ring
  apply (actual_det_of_scalar n hn (P+δ) h1).trans
  apply (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le).trans
  rw [←Real.exp_add,Real.exp_le_exp,hrel]
  have err := (div_lt_iff₀ hN).mp h2
  change (B+δ)*normalizer n+_≤_
  have gap : B+δ+δ-4/5*energy+(P+δ)≤ -619/100 := by dsimp [δ] at *; linarith only [hp]
  nlinarith only [mul_le_mul_of_nonneg_right gap hN.le,err]

end OddZetaSix.B40a.Witness
