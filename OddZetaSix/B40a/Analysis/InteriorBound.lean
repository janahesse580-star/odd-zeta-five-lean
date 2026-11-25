import OddZetaSix.B40a.Analysis.ChordPhase
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Cert.Chord Finset

def fieldOn (z w : Pt) (t : ℝ) :=
  phaseReal (lerp t z.1 w.1) (lerp t z.2 w.2)+(8/5)*potential (((1-t) • emb z+t • emb w)^2)

private theorem pot_chord (z w : Pt) {t : ℝ} (h0 : 0≤t) (h1 : t≤1) :
    potential (((1-t) • emb z+t • emb w)^2) ≤
    (1-t)*potential ((emb z)^2)+t*potential ((emb w)^2)+(1-t)*t*(cSum z w:ℝ)/fix := by
  have hS : ∑ i : Index,(cc z w (entry i):ℝ)=(cSum z w:ℝ) := by
    exact_mod_cast sum_entries (cc z w)
  have H := sum_le_sum (s:=univ) (fun i _=>circle_chord z w i h0 h1)
  simp only [lerp,sum_add_distrib,←mul_sum,←sum_div,hS] at H
  exact H

private theorem upper_node (q : ℤ) (hq : nodeOK q=true) : nodeField q≤(endpoint lookup circles q:ℝ)/fix := by
  have F : 0<(fix:ℝ) := by norm_num [fix]
  apply (le_div_iff₀ F).mpr
  rw [mul_comm]
  exact endpoint_sound q (of_decide_eq_true hq).1

theorem field_on_budget (p : Panel) (hp : p∈panelsRows) (hB : budget p)
    {t : ℝ} (h0 : 0≤t) (h1 : t≤1) :
    fieldOn (contourZ p.a) (contourZ p.b) t≤(peak:ℝ)/fix := by
  let z := contourZ p.a
  let w := contourZ p.b
  have F : 0<(fix:ℝ) := by norm_num [fix]
  obtain ⟨hy,hor,hgeom,hbudget⟩ := hB
  have P := phase_chord z w h0 h1 hy hor (fun v h=>of_decide_eq_true (List.all_eq_true.mp hgeom v h))
  have U := pot_chord z w h0 h1
  have B := List.all_eq_true.mp endpoints_checked p hp
  simp only [Bool.and_eq_true] at B
  obtain ⟨hA,hB'⟩ := B
  let M : ℝ := max (endpoint lookup circles p.a) (endpoint lookup circles p.b)
  let K : ℝ := (phSum z w:ℝ)+(8/5)*(cSum z w:ℝ)
  have R : 20*M+5*(phSum z w:ℝ)+8*(cSum z w:ℝ)≤20*(peak:ℝ) := by dsimp [M,z,w]; exact_mod_cast hbudget
  have Z : (emb z)^2=squarePoint z.1 z.2 := by simp [emb,squarePoint]
  have W : (emb w)^2=squarePoint w.1 w.2 := by simp [emb,squarePoint]
  have C : fieldOn z w t≤(1-t)*nodeField p.a+t*nodeField p.b+(1-t)*t*K/fix := by
    unfold fieldOn
    rw [Z,W] at U
    change _ ≤ (1-t)*(phaseReal z.1 z.2+(8/5)*potential (squarePoint z.1 z.2))+
      t*(phaseReal w.1 w.2+(8/5)*potential (squarePoint w.1 w.2))+(1-t)*t*K/fix
    unfold K
    linear_combination P+(8/5)*U
  have sumle (A D e : ℝ) (hA : A≤e) (hD : D≤e) : (1-t)*A+t*D≤e := by
    have I := add_le_add (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr h1)) (mul_le_mul_of_nonneg_left hD h0)
    apply I.trans_eq; ring
  have hM : (1-t)*nodeField p.a+t*nodeField p.b≤M/fix := by
    apply sumle
    · exact (upper_node _ hA).trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) F.le)
    · exact (upper_node _ hB').trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) F.le)
  have hT : 0≤(1-t)*t := mul_nonneg (sub_nonneg.mpr h1) h0
  apply C.trans
  by_cases hk : 0≤K
  · have hq : (1-t)*t≤1/4 := by nlinarith only [sq_nonneg (t-1/2)]
    have step := add_le_add hM (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq hk) F.le)
    apply step.trans
    rw [←add_div,div_le_div_iff_of_pos_right F]
    unfold K; linarith only [R]
  · have hn := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hT (le_of_not_ge hk)) F.le
    have hn' := endpoints_real_bound hp
    exact (add_le_of_nonpos_right hn).trans (sumle _ _ _ hn'.1 hn'.2)
end OddZetaSix.B40a.Witness
