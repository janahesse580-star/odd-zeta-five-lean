import OddZetaSix.B40a.Analysis.AngleIntervals

noncomputable section
namespace OddZetaSix.B40a.Cert
open Real

def primReal (x y : ℝ) := x/2*Real.log (x*x+y*y)-x+
  y*(if y=0 then Real.pi*(if 0<x then 1/2 else -1/2) else Real.arctan (x/y))

private theorem linear_box (x : ℚ) : Encloses ⟨qfloor (-x*fix),qceil (-x*fix)⟩ (-(x:ℝ)) := by
  have l := floor_bound (-x*fix); have h := ceil_bound (-x*fix); push_cast at l h
  exact ⟨l.trans_eq (by ring),(by ring : (fix:ℝ)*(-x) = -x*fix) ▸ h⟩

theorem phasePrimitive_sound (x y : ℚ) : Encloses (phasePrimitive x y) (primReal x y) := by
  have angle : Encloses (if y=0 then scale piBounds (if 0<x then 1/2 else -1/2) else atanBounds (x/y))
      (if (y:ℝ)=0 then Real.pi*(if (0:ℝ)<x then 1/2 else -1/2) else Real.arctan ((x:ℝ)/y)) := by
    by_cases hy : y=0
    · subst y
      by_cases hx : 0<x
      · have hR : (0:ℝ)<x := by exact_mod_cast hx
        simpa [hx,hR,mul_comm] using piBounds_sound.mul_rat (1/2)
      · have hR : ¬(0:ℝ)<x := by exact_mod_cast hx
        simpa [hx,hR,mul_comm] using piBounds_sound.mul_rat (-1/2)
    · have hR : (y:ℝ)≠0 := by exact_mod_cast hy
      simpa [hy,hR] using atanBounds_sound (x/y)
  have logbox : Encloses (scale (logRat (x*x+y*y)) (x/2)) ((x:ℝ)/2*Real.log (x*x+y*y)) := by
    by_cases hp : 0<x*x+y*y
    · simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using (logRat_sound _ hp).mul_rat (x/2)
    · have hx : x=0 := by nlinarith [sq_nonneg y,sq_nonneg x]
      have hy : y=0 := by nlinarith [sq_nonneg y,sq_nonneg x]
      subst x; subst y; norm_num [Encloses,scale,qfloor,qceil]
  simpa only [phasePrimitive,primReal,sub_eq_add_neg] using (logbox.add (linear_box x)).add (angle.mul_rat y)

def termReal (x y : ℝ) (b : ℤ×ℤ×ℤ) : ℝ :=
  let w := ((b.2.1:ℝ)-b.1)/100
  (b.2.2:ℝ)*((primReal (x+(b.2.1-118)/100) y-primReal (x+(b.1-118)/100) y)-w*(Real.log w-1))

def phaseReal (x y : ℝ) := -2*y*Real.pi+(phaseBlocks.map (termReal x y)).sum

private theorem all_widths : phaseBlocks.all (fun b=>decide (b.1<b.2.1))=true := by decide +kernel

private def termBox (x y : ℚ) (t : ℤ×ℤ×ℤ) :=
  let w := qfrac (t.2.1-t.1) 100
  let width := scale (plus (logRat w) ⟨-fix,-fix⟩) (-w)
  let p := plus (phasePrimitive (x+qfrac (t.2.1-118) 100) y)
    (scale (phasePrimitive (x+qfrac (t.1-118) 100) y) (-1))
  scale (plus p width) (t.2.2:ℚ)

private theorem term_sound (x y : ℚ) (t : ℤ×ℤ×ℤ) (ht : t∈phaseBlocks) :
    Encloses (termBox x y t) (termReal x y t) := by
  have hb := of_decide_eq_true (List.all_eq_true.mp all_widths t ht)
  let w := qfrac (t.2.1-t.1) 100
  have hp : 0<w := by unfold w qfrac; apply div_pos _ (by norm_num); exact_mod_cast sub_pos.mpr hb
  have hm : Encloses ⟨-fix,-fix⟩ (-1) := by norm_num [Encloses,fix]
  have wd := ((logRat_sound _ hp).add hm).mul_rat (-w)
  have a := phasePrimitive_sound (x+qfrac (t.2.1-118) 100) y
  have b := (phasePrimitive_sound (x+qfrac (t.1-118) 100) y).mul_rat (-1)
  have H := (((a.add b).add wd).mul_rat (t.2.2:ℚ))
  convert H using 1
  · rfl
  · simp [termReal,qfrac,w,sub_eq_add_neg] <;> ring

private theorem foldBox (x y : ℚ) (ts : List (ℤ×ℤ×ℤ)) (h : ∀ t∈ts,t∈phaseBlocks)
    (acc : Interval) (v : ℝ) (ha : Encloses acc v) :
    Encloses (ts.foldl (fun s t=>plus s (termBox x y t)) acc) (v+(ts.map (termReal x y)).sum) := by
  induction ts generalizing acc v with
  | nil => simpa
  | cons t ts ih =>
    have H := ih (fun z hz=>h z (List.mem_cons_of_mem _ hz)) _ _ (ha.add (term_sound x y t (h t List.mem_cons_self)))
    simpa only [List.foldl_cons,List.map_cons,List.sum_cons,add_assoc] using H

theorem phaseUpper_sound (k : ℤ) :
    (fix:ℝ)*phaseReal ((contourZ k).1:ℝ) ((contourZ k).2:ℝ)≤phaseUpper k := by
  let x := (contourZ k).1
  let y := (contourZ k).2
  have H := foldBox x y phaseBlocks (fun _ h=>h) _ _ (piBounds_sound.mul_rat (-2*y))
  have hb := H.2
  push_cast at hb
  exact hb
end OddZetaSix.B40a.Cert
