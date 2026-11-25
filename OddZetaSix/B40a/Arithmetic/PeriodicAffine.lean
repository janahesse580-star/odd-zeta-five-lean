import OddZetaSix.B40a.Arithmetic.PeriodicMidpoint

/-! Transport the period moments on each certificate interval by checking
affine inequalities at its two endpoints. Interval endpoints may be genuine
discontinuities in the inverse-prime variable. -/
namespace OddZetaSix.B40a.Cert
open Set MeasureTheory

namespace PeriodAffine

private theorem both {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  simpa only [Bool.and_eq_true] using h

abbrev Line := ℚ × ℚ
def val (l : Line) (t : ℚ) := l.1*t+l.2
def realVal (l : Line) (t : ℝ) := (l.1:ℝ)*t+(l.2:ℝ)
def endsLE (a b : ℚ) (l r : Line) : Bool := decide (val l a ≤ val r a ∧ val l b ≤ val r b)

theorem line_le {a b : ℚ} {l r : Line} (h : endsLE a b l r = true) {t : ℝ}
    (ht : t ∈ Icc (a:ℝ) b) : realVal l t ≤ realVal r t := by
  have H : val l a ≤ val r a ∧ val l b ≤ val r b := of_decide_eq_true h
  have h1 : realVal l (a:ℝ) ≤ realVal r (a:ℝ) := by
    simpa only [val,realVal,Rat.cast_add,Rat.cast_mul] using (Rat.cast_le (K:=ℝ)).mpr H.1
  have h2 : realVal l (b:ℝ) ≤ realVal r (b:ℝ) := by
    simpa only [val,realVal,Rat.cast_add,Rat.cast_mul] using (Rat.cast_le (K:=ℝ)).mpr H.2
  dsimp [realVal] at *
  by_cases hc : (l.1:ℝ) ≤ r.1
  · nlinarith only [h1,mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr ht.1)]
  · nlinarith only [h2,mul_nonneg (sub_nonneg.mpr (le_of_not_ge hc)) (sub_nonneg.mpr ht.2)]

def mid (r : ArithRow) := (r.left+r.right)/2
def floorAt (r : ArithRow) (l h : Line) (e : ℤ) : ℤ :=
  qfloor (e*mid r - (val l (mid r)+val h (mid r))/2)
def widthFloor (r : ArithRow) (e : ℤ) := qfloor (e*mid r)
def delta (e k : ℤ) (l : Line) : Line := (e-l.1,-l.2-k)
private def insertLine (t : ℚ) (x : Line) : List Line → List Line
  | [] => [x]
  | y::ys => if val x t < val y t then x::y::ys
             else if val x t = val y t then y::ys else y::insertLine t x ys

def periodLines (r : ArithRow) : List Line :=
  let t := mid r
  let xs : List Line := (0,0)::(0,1)::periodEnds.map (fun e => ((e:ℚ),-(qfloor (e*t):ℚ)))
  xs.foldl (fun s x => insertLine t x s) []
def cellCheck (r : ArithRow) (l h : Line) : Bool :=
  endsLE r.left r.right l h && periodEnds.all (fun e =>
    let k := floorAt r l h e
    endsLE r.left r.right (0,0) (delta e k h) &&
    endsLE r.left r.right (delta e k l) (0,1))

def widthCheck (r : ArithRow) : Bool :=
  ([25,32,34,50] : List ℤ).all (fun e =>
    let k := widthFloor r e
    decide ((k:ℚ) ≤ e*r.left ∧ e*r.right ≤ (k:ℚ)+1))
def chainCheck (r : ArithRow) (x : Line) : List (Line × Line) → Bool
  | [] => decide (x=(0,1))
  | (l,h)::xs => decide (x=l) && cellCheck r l h && chainCheck r h xs

def check (r : ArithRow) :=
  decide (r.left < r.right) && widthCheck r && chainCheck r (0,0) (adjacent (periodLines r))

def cellScore (r : ArithRow) (l h : Line) : ℤ :=
  let cnt (a b : ℤ) := floorAt r l h b - floorAt r l h a - widthFloor r (b-a)
  max 0 (4+6*cnt (-25) 25+4*cnt (-17) 17+2*cnt (-16) 16-5*cnt (-59) (-34)-5*cnt 34 59)

private theorem cell_score (r : ArithRow) (l h : Line) (hw : widthCheck r = true)
    (ok : cellCheck r l h = true) {t u : ℝ} (ht : t ∈ Ioo (r.left:ℝ) r.right)
    (hu : u ∈ Ioo (realVal l t) (realVal h t)) : periodicScore t u = cellScore r l h := by
  have checks := (both ok).2
  have hf (e : ℤ) (he : e ∈ periodEnds) : ⌊(e:ℝ)*t-u⌋ = floorAt r l h e := by
    have hsub := both (List.all_eq_true.mp checks e he)
    have h1 := line_le hsub.1 (Ioo_subset_Icc_self ht)
    have h2 := line_le hsub.2 (Ioo_subset_Icc_self ht)
    simp [realVal,delta] at h1 h2
    dsimp [realVal] at hu
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith [hu.1,hu.2]
  have hwidth (e : ℤ) (he : e ∈ ([25,32,34,50] : List ℤ)) :
      ⌊(e:ℝ)*t⌋ = widthFloor r e := by
    have hpos : (0:ℝ)<e := by simp at he; rcases he with h|h|h|h <;> subst e <;> norm_num
    have hends := of_decide_eq_true (List.all_eq_true.mp hw e he)
    have h1 : (widthFloor r e:ℝ) ≤ (e:ℝ)*r.left := by exact_mod_cast hends.1
    have h2 : (e:ℝ)*(r.right:ℝ) ≤ (widthFloor r e:ℝ)+1 := by exact_mod_cast hends.2
    exact Int.floor_eq_iff.mpr ⟨h1.trans (mul_le_mul_of_nonneg_left ht.1.le hpos.le),
      (mul_lt_mul_of_pos_left ht.2 hpos).trans_le h2⟩
  have hc (a b : ℤ) (ha : a ∈ periodEnds) (hb : b ∈ periodEnds)
      (hs : b-a ∈ ([25,32,34,50] : List ℤ)) :
      periodicCount a b t u = floorAt r l h b-floorAt r l h a-widthFloor r (b-a) := by
    unfold periodicCount
    rw [hf b hb,hf a ha,hwidth _ hs]
  unfold periodicScore cellScore
  rw [hc (-25) 25 (by decide) (by decide) (by decide),hc (-17) 17 (by decide) (by decide) (by decide),
    hc (-16) 16 (by decide) (by decide) (by decide),hc (-59) (-34) (by decide) (by decide) (by decide),
    hc 34 59 (by decide) (by decide) (by decide)]

/-- The coefficients of the affine integral for any transform of the score. -/
def sumLine (r : ArithRow) (F : ℤ → ℤ) : List (Line × Line) → Line
  | [] => (0,0)
  | (l,h)::xs =>
    let s : ℚ := F (cellScore r l h)
    let rest := sumLine r F xs
    ((h.1-l.1)*s+rest.1,(h.2-l.2)*s+rest.2)

private theorem chain_integral (r : ArithRow) (F : ℤ → ℤ) (hw : widthCheck r = true)
    (xs : List (Line × Line)) (x : Line) (ok : chainCheck r x xs = true)
    {t : ℝ} (ht : t ∈ Ioo (r.left:ℝ) r.right) :
    let f := fun u : ℝ => (F (periodicScore t u):ℝ)
    IntervalIntegrable f volume (realVal x t) 1 ∧
      (∫ u in (realVal x t)..1,f u) = realVal (sumLine r F xs) t := by
  let f := fun u : ℝ => (F (periodicScore t u):ℝ)
  induction xs generalizing x with
  | nil =>
    simp only [chainCheck,decide_eq_true_eq] at ok
    subst x
    simp [sumLine,realVal]
  | cons lh xs ih =>
    obtain ⟨l,h⟩ := lh
    simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at ok
    rcases ok with ⟨⟨rfl,hcell⟩,hrest⟩
    obtain ⟨hI,hJ⟩ := ih h hrest
    let v : ℝ := F (cellScore r x h)
    have hle := line_le (both hcell).1 (Ioo_subset_Icc_self ht)
    have heq : EqOn f (fun _ => v) (Ioo (realVal x t) (realVal h t)) := by
      intro u hu
      dsimp [f,v]
      rw [cell_score r x h hw hcell ht hu]
    have hi : IntervalIntegrable f volume (realVal x t) (realVal h t) :=
      (intervalIntegrable_congr_uIoo (uIoo_of_le hle ▸ heq)).mpr intervalIntegrable_const
    refine ⟨hi.trans hI,?_⟩
    change (∫ u in (realVal x t)..1,f u) = _
    rw [←intervalIntegral.integral_add_adjacent_intervals hi hI,
      intervalIntegral.integral_congr_Ioo_of_le hle heq,intervalIntegral.integral_const,smul_eq_mul,hJ]
    simp [sumLine,realVal,v]
    ring

theorem period_integral_affine (r : ArithRow) (ok : check r = true) (F : ℤ → ℤ)
    {t : ℝ} (ht : t ∈ Ioo (r.left:ℝ) r.right) :
    (∫ u in (0:ℝ)..1,(F (periodicScore t u):ℝ)) =
      realVal (sumLine r F (adjacent (periodLines r))) t := by
  have h := both ok
  simpa only [realVal,Rat.cast_zero,zero_mul,add_zero] using
    (chain_integral r F (both h.1).2 _ _ h.2 ht).2

end PeriodAffine
end OddZetaSix.B40a.Cert
