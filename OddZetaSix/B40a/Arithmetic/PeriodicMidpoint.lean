import OddZetaSix.B40a.Arithmetic.SmallPrimeIntegral
import OddZetaSix.B40a.Certificate.Arithmetic

/-! Checked midpoint strips for the B40a periodic certificate. Each recorded
interval verifies the two extremal inequalities for every endpoint floor. -/
namespace OddZetaSix.B40a.Cert
open Set MeasureTheory

def midpointFloor (e n d a b : ℤ) := (2*e*n-(a+b))/(2*d)

def stripScore (n d a b : ℤ) : ℤ :=
  let count (l r : ℤ) := midpointFloor r n d a b - midpointFloor l n d a b - (r-l)*n/d
  max 0 (4+6*count (-25) 25+4*count (-17) 17+2*count (-16) 16-
    5*count (-59) (-34)-5*count 34 59)

def scoreStep (n d : ℤ) (acc ab : ℤ × ℤ) : ℤ × ℤ :=
  let s := stripScore n d ab.1 ab.2
  (acc.1+(ab.2-ab.1)*s,acc.2+(ab.2-ab.1)*((s-1)^2/4))

def scoreEdges (t : ℚ) : List ℤ :=
  increasingZ (0::(t.den:ℤ)::periodEnds.map (fun e => (e*t.num)%(t.den:ℤ)))

def stripChain (n d : ℤ) (x : ℤ) : List (ℤ × ℤ) → Bool
  | [] => decide (x=d)
  | (a,b)::xs => decide (x=a ∧ a<b) && periodEnds.all (fun e =>
      let k := midpointFloor e n d a b
      decide (k*d ≤ e*n-b ∧ e*n-a ≤ (k+1)*d)) && stripChain n d b xs

def midpointOK (t : ℚ) := stripChain t.num t.den 0 (adjacent (scoreEdges t))

private theorem floor_div_int (m d : ℤ) (hd : 0<d) : ⌊(m:ℝ)/(d:ℝ)⌋ = m/d := by
  rw [←Rat.cast_intCast (α:=ℝ) m,←Rat.cast_intCast (α:=ℝ) d,←Rat.cast_div,Rat.floor_cast]
  lift d to ℕ using hd.le
  simpa only [Int.cast_natCast] using Rat.floor_intCast_div_natCast m d

private theorem strip_valid {n d a b : ℤ} (hd : 0<d)
    (ok : ∀ e ∈ periodEnds, midpointFloor e n d a b*d ≤ e*n-b ∧
      e*n-a ≤ (midpointFloor e n d a b+1)*d)
    {u : ℝ} (hu : u ∈ Ioc ((a:ℝ)/d) ((b:ℝ)/d)) :
    periodicScore ((n:ℝ)/d) u = stripScore n d a b := by
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  have ht (e : ℤ) (he : e ∈ periodEnds) :
      ⌊(e:ℝ)*((n:ℝ)/d)-u⌋ = midpointFloor e n d a b := by
    let k := midpointFloor e n d a b
    have hlow : (k:ℝ)*d ≤ (e:ℝ)*n-b := by exact_mod_cast (ok e he).1
    have hhi : (e:ℝ)*n-a ≤ ((k:ℝ)+1)*d := by exact_mod_cast (ok e he).2
    have h1 := (div_lt_iff₀ hdR).mp hu.1
    have h2 := (le_div_iff₀ hdR).mp hu.2
    rw [show (e:ℝ)*((n:ℝ)/d)-u=((e:ℝ)*n-u*d)/d by field_simp]
    exact Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hdR).mpr (by linarith),
      (div_lt_iff₀ hdR).mpr (by linarith)⟩
  have hc (l r : ℤ) (hl : l ∈ periodEnds) (hr : r ∈ periodEnds) :
      periodicCount l r ((n:ℝ)/d) u = midpointFloor r n d a b-midpointFloor l n d a b-(r-l)*n/d := by
    unfold periodicCount
    rw [ht r hr,ht l hl,show (((r-l:ℤ):ℝ))*((n:ℝ)/d)=((((r-l)*n:ℤ):ℝ))/(d:ℝ) by push_cast; ring,
      floor_div_int _ _ hd]
  unfold periodicScore stripScore
  rw [hc (-25) 25 (by decide) (by decide),hc (-17) 17 (by decide) (by decide),
    hc (-16) 16 (by decide) (by decide),hc (-59) (-34) (by decide) (by decide),
    hc 34 59 (by decide) (by decide)]

private def select (quadratic : Bool) (v : ℤ × ℤ) := if quadratic then v.2 else v.1
private def scoreTerm (quadratic : Bool) (s : ℤ) := if quadratic then (s-1)^2/4 else s

private theorem strip_sum_integral (n d : ℤ) (hd : 0<d) (quadratic : Bool)
    (xs : List (ℤ × ℤ)) (x : ℤ) (acc : ℤ × ℤ) (ok : stripChain n d x xs = true) :
    let f := fun u : ℝ => ((scoreTerm quadratic (periodicScore ((n:ℝ)/d) u):ℤ):ℝ)
    IntervalIntegrable f volume ((x:ℝ)/d) 1 ∧
      (∫ u in ((x:ℝ)/d)..1,f u) =
      ((select quadratic (xs.foldl (scoreStep n d) acc) - select quadratic acc : ℤ):ℝ)/d := by
  let f := fun u : ℝ => ((scoreTerm quadratic (periodicScore ((n:ℝ)/d) u):ℤ):ℝ)
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  induction xs generalizing x acc with
  | nil =>
    simp only [stripChain,decide_eq_true_eq] at ok
    subst x
    simp [hdR.ne']
  | cons ab xs ih =>
    obtain ⟨a,b⟩ := ab
    simp only [stripChain,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ok
    rcases ok with ⟨⟨⟨rfl,hab⟩,checks⟩,hok⟩
    obtain ⟨tailInt,tailEq⟩ := ih b (scoreStep n d acc (x,b)) hok
    let s := stripScore n d x b
    let v : ℝ := scoreTerm quadratic s
    have hle : (x:ℝ)/d ≤ (b:ℝ)/d := div_le_div_of_nonneg_right (by exact_mod_cast hab.le) hdR.le
    have hcell : EqOn f (fun _ => v) (Ioo ((x:ℝ)/d) ((b:ℝ)/d)) := by
      intro u hu
      dsimp [f,v,s]
      rw [strip_valid hd checks ⟨hu.1,hu.2.le⟩]
    have hcellInt : IntervalIntegrable f volume ((x:ℝ)/d) ((b:ℝ)/d) :=
      (intervalIntegrable_congr_uIoo (uIoo_of_le hle ▸ hcell)).mpr intervalIntegrable_const
    refine ⟨hcellInt.trans tailInt,?_⟩
    change (∫ u in ((x:ℝ)/d)..1,f u) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hcellInt tailInt,
      intervalIntegral.integral_congr_Ioo_of_le hle hcell, intervalIntegral.integral_const, smul_eq_mul]
    change _ + (∫ u in ((b:ℝ)/d)..1,f u) = _
    rw [tailEq]
    have step : select quadratic (scoreStep n d acc (x,b)) =
        select quadratic acc + (b-x)*scoreTerm quadratic s := by cases quadratic <;> rfl
    simp only [List.foldl_cons,step,Int.cast_sub,Int.cast_add,Int.cast_mul]
    dsimp [v]
    ring

/-- Soundness of the exact rational midpoint moments. A finite check covers
partition endpoints as well as both one-sided floor inequalities on every strip. -/
theorem periodScores_integrals_of_check (t : ℚ) (ok : midpointOK t = true) :
    ((periodScores t).1 : ℝ) = ∫ u in (0:ℝ)..1, (periodicScore (t:ℝ) u : ℝ) ∧
    ((periodScores t).2 : ℝ) = ∫ u in (0:ℝ)..1, (((periodicScore (t:ℝ) u-1)^2/4 : ℤ):ℝ) := by
  have hd : 0<(t.den:ℤ) := by exact_mod_cast t.den_pos
  have H (b : Bool) := (strip_sum_integral t.num t.den hd b
    (adjacent (scoreEdges t)) 0 (0,0) ok).2
  have ht : (t:ℝ)=(t.num:ℝ)/(t.den:ℝ) := Rat.cast_def t
  let acc := (adjacent (scoreEdges t)).foldl (scoreStep t.num (t.den:ℤ)) (0,0)
  have form : periodScores t = ((acc.1:ℚ)/(t.den:ℤ),(acc.2:ℚ)/(t.den:ℤ)) := rfl
  rw [form]
  dsimp only [Prod.fst,Prod.snd,acc]
  constructor
  · simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast,Int.cast_natCast,Int.cast_zero,zero_div,select,
      Bool.false_eq_true,ite_false,scoreTerm,sub_zero,ht] using (H false).symm
  · simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast,Int.cast_natCast,Int.cast_zero,zero_div,select,
      ite_true,scoreTerm,sub_zero,ht] using (H true).symm

end OddZetaSix.B40a.Cert
