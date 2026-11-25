import OddZetaSix.B40a.Analysis.InteriorBound
noncomputable section
namespace OddZetaSix.B40a.Cert.Chord
open Real Set
abbrev Band := (ℤ×ℤ)×(ℤ×ℤ)
def bands : List Band := adjacent knots
def bandRows (e : Band) := panelsRows.filter fun p=>decide (e.1.1≤p.a ∧ p.b≤e.2.1)
def baseX (a : ℤ) : ℚ := 118/100-(a:ℚ)/phaseTicks
def slope (e : Band) : ℚ := ((e.1.2:ℚ)-e.2.2)/((e.2.1:ℚ)-e.1.1)
def offset (e : Band) : ℚ := baseX e.1.2-slope e*(e.1.1:ℚ)/phaseTicks
def atQ (e : Band) (q : ℤ) : Prop :=
  (contourZ q).2=(q:ℚ)/phaseTicks ∧ (contourZ q).1=slope e*(contourZ q).2+offset e
instance (e : Band) (q : ℤ) : Decidable (atQ e q) := by unfold atQ; infer_instance
def goodBand (e : Band) := decide (e.1.1<e.2.1) && panelChain e.1.1 e.2.1 (bandRows e) &&
  (bandRows e).all fun p=>decide (p.a<p.b ∧ atQ e p.a ∧ atQ e p.b)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bands_checked : bands.all goodBand=true := by decide +kernel

private theorem chain_cover (ps : List Panel) {a b : ℤ} (h : panelChain a b ps=true)
    {y : ℝ} (hab : a<b) (ha : (a:ℝ)≤y) (hb : y≤(b:ℝ)) :
    ∃ p∈ps,(p.a:ℝ)≤y ∧ y≤(p.b:ℝ) := by
  induction ps generalizing a with
  | nil =>
    have hh : a=b := of_decide_eq_true h
    omega
  | cons p ps ih =>
    simp only [panelChain,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases he : y≤(p.b:ℝ)
    · exact ⟨p,List.mem_cons_self,h.1 ▸ ha,he⟩
    · have hh : (p.b:ℝ)<y := lt_of_not_ge he
      obtain ⟨q,hq,H⟩ := ih h.2 (by exact_mod_cast hh.trans_le hb) hh.le
      exact ⟨q,List.mem_cons_of_mem _ hq,H⟩

theorem band_cover {e : Band} (he : e∈bands) {y : ℝ}
    (ha : (e.1.1:ℝ)/(phaseTicks:ℝ)≤y) (hb : y≤(e.2.1:ℝ)/(phaseTicks:ℝ)) :
    ∃ p∈panelsRows,∃ t : ℝ,0≤t ∧ t≤1 ∧
      lerp t (contourZ p.a).2 (contourZ p.b).2=y ∧
      lerp t (contourZ p.a).1 (contourZ p.b).1=(slope e:ℝ)*y+offset e := by
  have H := List.all_eq_true.mp bands_checked e he
  simp only [goodBand,Bool.and_eq_true,decide_eq_true_eq] at H
  have pos : (0:ℝ)<(phaseTicks:ℝ) := by norm_num [phaseTicks]
  obtain ⟨p,hp,hl,hr⟩ := chain_cover (bandRows e) H.1.2 H.1.1
    ((div_le_iff₀ pos).mp ha) ((le_div_iff₀ pos).mp hb)
  obtain ⟨hpab,hL,hR⟩ := of_decide_eq_true (List.all_eq_true.mp H.2 p hp)
  have hp' := (List.mem_filter.mp hp).1
  let a : ℝ := (contourZ p.a).2
  let b : ℝ := (contourZ p.b).2
  have A : a=(p.a:ℝ)/(phaseTicks:ℝ) := by dsimp [a]; exact_mod_cast hL.1
  have B : b=(p.b:ℝ)/(phaseTicks:ℝ) := by dsimp [b]; exact_mod_cast hR.1
  have ay : a≤y := A ▸ ((div_le_iff₀ pos).mpr hl)
  have yb : y≤b := B ▸ ((le_div_iff₀ pos).mpr hr)
  have ab : a<b := by rw [A,B]; exact div_lt_div_of_pos_right (by exact_mod_cast hpab) pos
  let t := (y-a)/(b-a)
  have V : t*(b-a)=y-a := div_mul_cancel₀ _ (sub_pos.mpr ab).ne'
  have E : lerp t a b=y := by unfold lerp; linarith only [V]
  have XL : ((contourZ p.a).1:ℝ)=(slope e:ℝ)*a+offset e := by dsimp [a]; exact_mod_cast hL.2
  have XR : ((contourZ p.b).1:ℝ)=(slope e:ℝ)*b+offset e := by dsimp [b]; exact_mod_cast hR.2
  refine ⟨p,hp',t,div_nonneg (sub_nonneg.mpr ay) (sub_pos.mpr ab).le,(div_le_one (sub_pos.mpr ab)).mpr (by linarith),E,?_⟩
  rw [XL,XR,←E]; unfold lerp; ring
end OddZetaSix.B40a.Cert.Chord
