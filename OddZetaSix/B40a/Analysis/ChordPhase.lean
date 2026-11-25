import OddZetaSix.B40a.Analysis.ChordGeometry
noncomputable section
namespace OddZetaSix.B40a.Cert.Chord
open Real Set
private theorem rectX {lo hi x : ℝ} (h1 : lo≤x) (h2 : x≤hi) :
    max 0 (max lo (-hi))≤|x| :=
  max_le (abs_nonneg _) (max_le (h1.trans (le_abs_self _)) ((neg_le_neg h2).trans (neg_le_abs x)))

private theorem line_range (m c a b y : ℝ) (h : y∈Icc a b) :
    min (lineX m c a) (lineX m c b)≤lineX m c y ∧ lineX m c y≤max (lineX m c a) (lineX m c b) := by
  unfold lineX
  by_cases hm : 0≤m
  · exact ⟨(min_le_left _ _).trans (by linarith only [mul_le_mul_of_nonneg_left h.1 hm]),
      (show m*y+c≤m*b+c by linarith only [mul_le_mul_of_nonneg_left h.2 hm]).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (by linarith only [mul_le_mul_of_nonpos_left h.2 (le_of_not_ge hm)]),
      (show m*y+c≤m*a+c by linarith only [mul_le_mul_of_nonpos_left h.1 (le_of_not_ge hm)]).trans (le_max_left _ _)⟩

private theorem shifted_chord (z w : Pt) (p k : ℤ) {t : ℝ} (h0 : 0≤t) (h1 : t≤1)
    (hy : 0≤z.2) (hor : z.2<w.2) (hp : 0<phaseD z w p) :
    let s : ℝ := ((p:ℝ)-118)/100
    (k:ℝ)*primReal (lerp t z.1 w.1+s) (lerp t z.2 w.2) ≤
      lerp t ((k:ℝ)*primReal ((z.1:ℝ)+s) z.2) ((k:ℝ)*primReal ((w.1:ℝ)+s) w.2)+
        (1-t)*t*(cp z w p k:ℝ)/fix := by
  let a : ℝ := z.2
  let b : ℝ := w.2
  let s : ℝ := ((p:ℝ)-118)/100
  let m : ℝ := ((w.1:ℝ)-z.1)/(b-a)
  let c : ℝ := (z.1:ℝ)+s-m*a
  let d : ℝ := phaseD z w p
  have hab : a<b := by dsimp [a,b]; exact_mod_cast hor
  have ha : 0≤a := by dsimp [a]; exact_mod_cast hy
  have hd : 0<d := by dsimp [d]; exact_mod_cast hp
  have hs : m*(b-a)=(w.1:ℝ)-z.1 := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have ea : lineX m c a=(z.1:ℝ)+s := by unfold lineX c; ring
  have eb : lineX m c b=(w.1:ℝ)+s := by unfold lineX c; linarith only [hs]
  have em : lineX m c (lerp t a b)=lerp t z.1 w.1+s := by
    unfold lineX lerp c; linear_combination t*hs
  let xlo : ℚ := max 0 (max (min (z.1+((p:ℚ)-118)/100) (w.1+((p:ℚ)-118)/100))
      (-max (z.1+((p:ℚ)-118)/100) (w.1+((p:ℚ)-118)/100)))
  have Hlow (y : ℝ) (hh : y∈Icc a b) : d^2≤lineQ m c y := by
    have hroot := root_lower (xlo^2+z.2^2) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hr : d^2≤(xlo:ℝ)^2+a^2 := by change (rootLo (xlo^2+z.2^2):ℝ)^2 ≤ (xlo:ℝ)^2+(z.2:ℝ)^2; exact_mod_cast hroot
    obtain ⟨H1,H2⟩ := line_range m c a b y hh
    rw [ea,eb] at H1 H2
    have hx : (xlo:ℝ)≤|lineX m c y| := by
      convert rectX H1 H2 using 1; simp [xlo,s]
    have hx0 : (0:ℝ)≤xlo := by exact_mod_cast (le_max_left 0 _)
    have H := pow_le_pow_left₀ hx0 hx 2
    rw [sq_abs] at H
    exact hr.trans (add_le_add H (pow_le_pow_left₀ ha hh.1 2))
  have C := (signed_phase_convex m c a b (k:ℝ) d ha hd Hlow).2
    (show a∈Icc a b from ⟨le_rfl,hab.le⟩) (show b∈Icc a b from ⟨hab.le,le_rfl⟩)
    (sub_nonneg.mpr h1) h0 (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at C
  change _*linePrim m c (lerp t a b)+_≤_ at C
  simp only [linePrim,ea,eb,em] at C
  let K : ℝ := |(k:ℝ)| *(1+m^2)/d
  have id1 : K*((1-t)*a^2+t*b^2-(lerp t a b)^2)/2=(1-t)*t*(K*(b-a)^2/2) := by unfold lerp; ring
  have id2 : K*(b-a)^2/2= |(k:ℝ)| *(dist2 z w:ℝ)/(2*d) := by
    have V : (1+m^2)*(b-a)^2=(dist2 z w:ℝ) := by
      simp only [dist2,mag,Rat.cast_add,Rat.cast_pow,Rat.cast_sub]
      nlinarith only [congrArg (fun u : ℝ=>u^2) hs]
    unfold K; rw [←V]; ring
  have M := ceil_bound ((fix:ℚ)*k.natAbs*dist2 z w/(2*phaseD z w p))
  push_cast at M
  have hk : (k.natAbs:ℝ)=|(k:ℝ)| := by rw [←Int.cast_abs,←Int.natCast_natAbs]; simp
  rw [hk] at M
  have F : 0<(fix:ℝ) := by norm_num [fix]
  have V : K*(b-a)^2/2 ≤ (cp z w p k:ℝ)/fix := by
    rw [id2,le_div_iff₀ F]; calc _ = _ := by ring
                                  _ ≤ _ := M
  have J := mul_le_mul_of_nonneg_left V (mul_nonneg (sub_nonneg.mpr h1) h0)
  dsimp only
  change (k:ℝ)*primReal (lerp t z.1 w.1+s) (lerp t a b)≤_
  change (k:ℝ)*primReal (lerp t z.1 w.1+s) (lerp t a b)+K*(lerp t a b)^2/2≤
    (1-t)*(_+K*a^2/2)+t*(_+K*b^2/2) at C
  change _ ≤ (1-t)*((k:ℝ)*primReal ((z.1:ℝ)+s) a)+t*((k:ℝ)*primReal ((w.1:ℝ)+s) b)+(1-t)*t*(cp z w p k:ℝ)/fix
  linear_combination C+J+id1

def phaseCost (z w : Pt) (v : ℤ×ℤ×ℤ) := cp z w v.1 v.2.2+cp z w v.2.1 v.2.2

private theorem term_chord (z w : Pt) (v : ℤ×ℤ×ℤ) {t : ℝ} (h0 : 0≤t) (h1 : t≤1)
    (hy : 0≤z.2) (hor : z.2<w.2) (hp : 0<phaseD z w v.1 ∧ 0<phaseD z w v.2.1) :
    termReal (lerp t z.1 w.1) (lerp t z.2 w.2) v ≤
      (1-t)*termReal z.1 z.2 v+t*termReal w.1 w.2 v+(1-t)*t*(phaseCost z w v:ℝ)/fix := by
  have L := shifted_chord z w v.1 (-v.2.2) h0 h1 hy hor hp.1
  have R := shifted_chord z w v.2.1 v.2.2 h0 h1 hy hor hp.2
  dsimp only at L R
  have neg_cp : cp z w v.1 (-v.2.2)=cp z w v.1 v.2.2 := by simp [cp]
  rw [Int.cast_neg,neg_cp] at L
  unfold termReal phaseCost
  rw [Int.cast_add]
  dsimp only [lerp] at L R ⊢
  linear_combination L+R

theorem phase_chord (z w : Pt) {t : ℝ} (h0 : 0≤t) (h1 : t≤1) (hy : 0≤z.2) (hor : z.2<w.2)
    (hp : ∀ v∈phaseBlocks,0<phaseD z w v.1 ∧ 0<phaseD z w v.2.1) :
    phaseReal (lerp t z.1 w.1) (lerp t z.2 w.2) ≤ (1-t)*phaseReal z.1 z.2+t*phaseReal w.1 w.2+
      (1-t)*t*(phSum z w:ℝ)/fix := by
  have aux (vs : List (ℤ×ℤ×ℤ)) (hvs : ∀ v∈vs,v∈phaseBlocks) :
      (vs.map (termReal (lerp t z.1 w.1) (lerp t z.2 w.2))).sum ≤
      (1-t)*(vs.map (termReal z.1 z.2)).sum+t*(vs.map (termReal w.1 w.2)).sum+
      (1-t)*t*(((vs.map (phaseCost z w)).sum:ℤ):ℝ)/fix := by
    induction vs with
    | nil => simp
    | cons v vs ih =>
      have H := term_chord z w v h0 h1 hy hor (hp _ (hvs _ List.mem_cons_self))
      have I := ih (fun v h=>hvs _ (List.mem_cons_of_mem _ h))
      simp only [List.map_cons,List.sum_cons,Int.cast_add]
      linear_combination H+I
  have H := aux phaseBlocks (fun _ h=>h)
  unfold phaseReal phSum
  change _ ≤ _+_+(1-t)*t*(((phaseBlocks.map (phaseCost z w)).sum:ℤ):ℝ)/fix
  dsimp only [lerp] at H ⊢
  linear_combination H
end OddZetaSix.B40a.Cert.Chord
