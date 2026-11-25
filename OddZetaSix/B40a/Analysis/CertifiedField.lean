import OddZetaSix.B40a.Analysis.ChordChecks
import OddZetaSix.B40a.Analysis.ContourCover
import OddZetaSix.B40a.Analysis.RayTail
import OddZetaSix.B40a.Analysis.FieldDrift
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Cert.Chord ComplexConjugate

/-- All real interpolation weights in each of the 119 certified pieces. -/
theorem panel_field_bound (p : Panel) (hp : p∈panelsRows) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    fieldOn (contourZ p.a) (contourZ p.b) t≤(peak:ℝ)/fix :=
  field_on_budget p hp (of_decide_eq_true (List.all_eq_true.mp budgets_checked p hp)) ht.1 ht.2

def limitingField (s : Bool) (x y : ℝ) := phaseReal x y+(8/5)*potential ((pointAt s x y)^2)

private theorem field_symm (x y : ℝ) (s : Bool) : limitingField s x y=limitingField true x y := by
  cases s with
  | true => rfl
  | false =>
    have e : pointAt false x y=conj (pointAt true x y) := by
      apply Complex.ext <;> simp [contourSide,pointAt]
    simp only [limitingField,e,←map_pow,potential_conj]

theorem band_field_bound (s : Bool) {e : Band} (he : e∈bands) {y : ℝ}
    (ha : (e.1.1:ℝ)/(phaseTicks:ℝ)≤y) (hb : y≤(e.2.1:ℝ)/(phaseTicks:ℝ)) :
    limitingField s ((slope e:ℝ)*y+offset e) y ≤ (peak:ℝ)/fix := by
  obtain ⟨p,hp,t,h0,h1,hy,hx⟩ := band_cover he ha hb
  have H := panel_field_bound p hp ⟨h0,h1⟩
  rw [field_symm]
  let z := contourZ p.a
  let w := contourZ p.b
  have Z : (1-t) • emb z+t • emb w=pointAt true (lerp t z.1 w.1) (lerp t z.2 w.2) := by
    apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,
      emb,pointAt,contourSide,lerp]
  change phaseReal (lerp t z.1 w.1) (lerp t z.2 w.2)+(8/5)*potential (((1-t) • emb z+t • emb w)^2)≤_ at H
  rw [Z] at H
  change lerp t z.1 w.1=_ at hx
  change lerp t z.2 w.2=_ at hy
  rw [hx,hy] at H
  exact H

theorem tail_field_bound (s : Bool) (y : ℝ) (hy : 4≤y) :
    limitingField s (327/200) y ≤ (peak:ℝ)/fix-6*(y-4) := by
  rw [field_symm]
  simpa [limitingField,rayZ,pointAt,contourSide] using ray_field_decay y hy
end OddZetaSix.B40a.Witness
