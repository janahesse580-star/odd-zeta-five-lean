import OddZetaSix.B40a.Arithmetic.SmallBandCover
import OddZetaSix.B40a.Arithmetic.SmallRowBudget

noncomputable section
namespace OddZetaSix.B40a
open Finset Filter MeasureTheory Set Cert Cert.PeriodAffine
open scoped Topology
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
attribute [local irreducible] smallRows

private theorem tileIntegral_cost (K : ℕ) :
    (∑ i ∈ smallTiles K, ∫ P in tileLo i..tileHi i, tileW i P) /2000 ≤
      (60166783595/1000000000000 : ℝ) := by
  unfold smallTiles
  rw [Finset.sum_sigma]
  have hs := sum_le_sum (s:=(univ:Finset SmallIndex)) (fun i _ => smallRow_budget (smallRow i) (smallRow_mem i) K)
  have hval : (∑ i : SmallIndex,rowValue true (smallRow i)) = (smallRows.map (rowValue true)).sum := by
    rw [←List.sum_ofFn]
    exact List.ofFn_getElem_eq_map smallRows (rowValue true) |> congrArg List.sum
  have hb := small_certified_row_sum
  rw [←hval,small_rows_total] at hb
  have hbR := (Rat.cast_le (K:=ℝ)).mpr hb
  rw [Rat.cast_sum] at hbR
  rw [←Finset.mul_sum] at hs
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2000)).mpr
  apply hs.trans
  have hnum : (↑((60166783595:ℚ)/(bigUnit:ℚ)):ℝ)=60166783595/1000000000000 := by norm_num [bigUnit]
  norm_num [bigUnit] at hbR
  linarith only [hbR]

private theorem tileW_nonneg {K : ℕ} {i : SmallTile} (hi : i ∈ smallTiles K)
    {P : ℝ} (hP : P ∈ Icc (tileLo i) (tileHi i)) : 0 ≤ tileW i P := by
  have hp := (tile_endpoints hi).1.trans_le hP.1
  let r := smallRow i.1
  have hr := smallRow_bounds r (smallRow_mem _)
  have hR : (r.left:ℝ)<r.right := by exact_mod_cast hr.2.1
  have hcheck := List.all_eq_true.mp smallRows_affine_check r (smallRow_mem _)
  have hCont (L : Line) : Continuous (realVal L) := by unfold realVal; fun_prop
  have closed : IsClosed {t : ℝ | 0 ≤ linearProfile r t ∧ 0 ≤ squareProfile r t} :=
    (isClosed_le continuous_const (hCont _)).inter (isClosed_le continuous_const (hCont _))
  have incl : Ioo (r.left:ℝ) (r.right:ℝ) ⊆ {t : ℝ | 0 ≤ linearProfile r t ∧ 0 ≤ squareProfile r t} := by
    intro t ht
    constructor
    · rw [linearProfile,← period_integral_affine r hcheck _ ht]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
        dsimp [linearTerm]; exact_mod_cast (periodicScore_bounds t u).1)
    · rw [squareProfile,← period_integral_affine r hcheck _ ht]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
        dsimp [squareTerm]; exact_mod_cast Int.ediv_nonneg (sq_nonneg _) (by decide : (0:ℤ)≤4))
  have hclosure := closure_minimal incl closed
  rw [closure_Ioo hR.ne] at hclosure
  obtain ⟨hF,hG⟩ := hclosure (tile_bounds_inverse hi hP)
  change 0 ≤ 40*linearProfile r _ + P/2*(linearProfile r _ + squareProfile r _)
  exact add_nonneg (mul_nonneg (by norm_num) hF) (mul_nonneg (by positivity) (add_nonneg hF hG))

theorem small_prime_cutoff_rate (K : ℕ) (hK : 17≤ K) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, bandPrimeCost n (1/(K:ℝ)) (11/20) / normalizer n ≤
      60166783595/1000000000000 + δ := by
  let ε := 1/(K:ℝ)
  have hKr : (17:ℝ)≤K := by exact_mod_cast hK
  have hε : 0<ε := one_div_pos.mpr (by linarith)
  have hεb : ε≤11/20 := (div_le_iff₀ (by linarith : 0<(K:ℝ))).mpr (by linarith)
  have H := bandPrimeCost_rate_of_piecewise_majorant (smallTiles K) ε (11/20) hε hεb
    tileLo tileHi tileW (fun i hi => (tile_endpoints hi).1) (fun i hi => (tile_endpoints hi).2.1)
    (fun i hi => (tile_endpoints hi).2.2)
    (fun i hi => smallTileWeight_continuous _ _ _ _ (tile_endpoints hi).1)
    (fun i hi P hP => tileW_nonneg hi hP)
    (7680/ε+432) (by positivity) (smallExceptional K) (smallTiles K).card
    (fun _ => inter_subset_right) (Eventually.of_forall fun _ => Finset.card_le_card Finset.inter_subset_left |>.trans Finset.card_image_le)
    (by
      filter_upwards [eventually_gt_atTop (84*K*K)] with n hn
      have hn0 : 0<n := by omega
      have hnR : 0<(n:ℝ) := by exact_mod_cast hn0
      intro p hp hexc
      have hc := Finset.mem_filter.mp hp
      have hpr := (Nat.mem_primesLE.mp hc.1).2
      have upper : (p:ℝ)≤11/20*(n:ℝ) :=
        (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hc.1).1
      obtain ⟨i,hi,hl,hh,ht⟩ := small_band_cover hK hn0 hpr hc.2 upper hexc
      refine ⟨i,hi,hl,hh,?_⟩
      have hnp : n<p*K := by
        have hnpR := (div_lt_iff₀ (by linarith : 0<(K:ℝ))).mp
          (by simpa [ε,div_eq_inv_mul] using hc.2 : (n:ℝ)/K < p)
        exact_mod_cast hnpR
      have hpK : 84*K<p := lt_of_mul_lt_mul_right (hn.trans hnp) (Nat.zero_le _)
      have hsq : 84*n<p^2 := by
        have H1 := Nat.mul_lt_mul_of_pos_left hnp (by decide : 0<84)
        have H2 := Nat.mul_lt_mul_of_pos_right hpK hpr.pos
        nlinarith only [H1,H2]
      letI : Fact p.Prime := ⟨hpr⟩
      exact primeExponent_le_small_tile n p i.2 hn0 hsq ε hε hc.2.le (smallRow i.1)
        (List.all_eq_true.mp smallRows_affine_check _ (smallRow_mem _)) ht)
    δ hδ
  filter_upwards [H] with n h
  exact h.trans (add_le_add_left (tileIntegral_cost K) _)

end OddZetaSix.B40a
