import OddZetaSix.B40a.Analysis.ChordBudget
import OddZetaSix.B40a.Analysis.PhaseCurvature
import OddZetaSix.B40a.Analysis.CheckedEndpoints
noncomputable section
namespace OddZetaSix.B40a.Cert.Chord
open Real Set

def emb (z : Pt) : ℂ := ((z.1:ℝ):ℂ)+((z.2:ℝ):ℂ)*Complex.I
def lerp (t a b : ℝ) := (1-t)*a+t*b

theorem sq_dist (z w : Pt) : ‖emb z-emb w‖^2=(dist2 z w:ℝ) := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [emb,dist2,mag,pow_two,Complex.sub_re,Complex.sub_im]

theorem emb_sq (z : Pt) : emb (sqPt z)=(emb z)^2 := by
  apply Complex.ext <;>
    simp [emb,sqPt,pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

theorem root_lower (q : ℚ) (hq : 0≤q) : rootLo q^2≤q := by
  let a := q*(coord:ℚ)^2
  have hn : 0≤qfloor a := by rw [qfloor_eq_floor]; exact Int.floor_nonneg.mpr (mul_nonneg hq (sq_nonneg _))
  have hf : (qfloor a:ℚ)≤a := by rw [qfloor_eq_floor]; exact Int.floor_le _
  have hh := Nat.sqrt_le' (qfloor a).toNat
  have hZ : (((qfloor a).toNat.sqrt:ℤ)^2)≤qfloor a := by exact_mod_cast (Int.toNat_of_nonneg hn) ▸ (show (((qfloor a).toNat.sqrt:ℤ)^2)≤(((qfloor a).toNat:ℕ):ℤ) by exact_mod_cast hh)
  have hR : (((qfloor a).toNat.sqrt:ℚ)^2)≤(qfloor a:ℚ) := by exact_mod_cast hZ
  unfold rootLo
  rw [div_pow,div_le_iff₀ (by norm_num [coord] : (0:ℚ)<(coord:ℚ)^2)]
  exact hR.trans hf

theorem radiusAt (z w : Pt) (i : Witness.Index) :
    let c := Witness.entry i
    let d : ℝ := circleD z w c
    Witness.r i≤d ∧ max d ‖emb z^2-Witness.u i‖=max (Witness.r i) ‖emb z^2-Witness.u i‖ ∧
      max d ‖emb w^2-Witness.u i‖=max (Witness.r i) ‖emb w^2-Witness.u i‖ := by
  let c := Witness.entry i
  let q := min (dist2 (sqPt z) (center c)) (dist2 (sqPt w) (center c))
  have dc : emb (center c)=Witness.u i := by simp [emb,center,Witness.u,c]
  have dr : (radius c:ℝ)=Witness.r i := by simp [radius,Witness.r,c]
  have hp (v : Pt) : 0≤dist2 (sqPt v) (center c) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hr := root_lower q (le_min (hp z) (hp w))
  have root_norm (v : Pt) (h : q≤dist2 (sqPt v) (center c)) : (rootLo q:ℝ)≤‖emb v^2-Witness.u i‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [←emb_sq,←dc,sq_dist]
    exact_mod_cast hr.trans h
  have he (v : Pt) (h : q≤dist2 (sqPt v) (center c)) :
      max (max (Witness.r i) (rootLo q:ℝ)) ‖emb v^2-Witness.u i‖=max (Witness.r i) ‖emb v^2-Witness.u i‖ := by
    rw [max_assoc,max_eq_right (root_norm v h)]
  change Witness.r i≤(circleD z w c:ℝ) ∧ _
  change _ ∧ max (circleD z w c:ℝ) _ = _ ∧ max (circleD z w c:ℝ) _ = _
  simp only [circleD,Rat.cast_max,dr]
  exact ⟨le_max_left _ _,he z (min_le_left _ _),he w (min_le_right _ _)⟩

theorem circle_chord (z w : Pt) (i : Witness.Index) {t : ℝ} (h0 : 0≤t) (h1 : t≤1) :
    let c := Witness.entry i
    let v := (1-t) • (emb z)+t • (emb w)
    Witness.b i*circlePotential (Witness.u i) (Witness.r i) (v^2) ≤
      lerp t (Witness.b i*circlePotential (Witness.u i) (Witness.r i) ((emb z)^2))
        (Witness.b i*circlePotential (Witness.u i) (Witness.r i) ((emb w)^2))+
      (1-t)*t*(cc z w c:ℝ)/fix := by
  let c := Witness.entry i
  let d : ℝ := circleD z w c
  let k := (1-t)*t
  have hk : 0≤k := mul_nonneg (sub_nonneg.mpr h1) h0
  obtain ⟨hdr,hz,hw⟩ := radiusAt z w i
  have hd : 0<d := (Witness.valid i).1.trans_le hdr
  have H := clipped_square_chord (emb z) (emb w) (Witness.u i) hd (sub_nonneg.mpr h1) h0 (by ring : 1-t+t=1)
  unfold circlePotential at H
  rw [hz,hw,←emb_sq,←emb_sq,sq_dist,sq_dist] at H
  have G := Real.log_le_log ((Witness.valid i).1.trans_le (le_max_left _ _))
    (max_le_max_right ‖((1-t) • emb z+t • emb w)^2-Witness.u i‖ hdr)
  have W := mul_le_mul_of_nonneg_left (G.trans H) (Witness.valid i).2
  have M := ceil_bound ((fix:ℚ)*c.mass/(2*massTotal)*(dist2 (sqPt z) (sqPt w)/(2*(circleD z w c)^2)+dist2 z w/(circleD z w c)))
  push_cast at M
  have F : 0<(fix:ℝ) := by norm_num [fix]
  have B : Witness.b i*((dist2 (sqPt z) (sqPt w):ℝ)/(2*d^2)+(dist2 z w:ℝ)/d) ≤ (cc z w c:ℝ)/fix := by
    apply (le_div_iff₀ F).mpr
    unfold Witness.b
    calc _ = _ := by ring
         _ ≤ _ := M
  dsimp only
  unfold lerp circlePotential
  rw [emb_sq,emb_sq] at W
  have V := mul_le_mul_of_nonneg_left B hk
  unfold k at V
  change _≤_+_*(cc z w c:ℝ)/fix
  apply W.trans
  let base := (1-t)*(Witness.b i*Real.log (max (Witness.r i) ‖emb z^2-Witness.u i‖))+t*(Witness.b i*Real.log (max (Witness.r i) ‖emb w^2-Witness.u i‖))
  convert add_le_add (le_refl base) V using 1 <;> unfold base <;> ring
end OddZetaSix.B40a.Cert.Chord
