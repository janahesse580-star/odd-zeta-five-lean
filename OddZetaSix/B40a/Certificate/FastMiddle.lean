import OddZetaSix.B40a.Arithmetic.MiddleClassSites
import OddZetaSix.B40a.Arithmetic.MiddleCapLayers
import OddZetaSix.B40a.Arithmetic.MiddleSweepRanks

namespace OddZetaSix.B40a.Cert

def fastCount (p d t a b : ℤ) : ℤ :=
  (b*d-t)/p - (a*d-t)/p

def siteMultiplicity (d t : ℤ) : ℕ :=
  6 + (if t < 17*d then 4 else 0) + (if t < 16*d then 2 else 0)

def fastSiteAtom (m : ℕ) (nd nz v : ℤ) (oddBad evenBad : Bool) (a e : ℕ) : ℤ :=
  let order := m-e-a
  let inc := if 0 < nd then (order : ℤ) else min (order : ℤ) nz
  let bad := if e%2 = 1 then oddBad else evenBad
  (a : ℤ)-v+inc+(if bad then (e : ℤ)+4 else 0)

def oddExtreme (n : ℕ) (bad : Bool) : ℕ :=
  if bad then n - ((n+1)%2) else 1

def evenExtreme (n : ℕ) (bad : Bool) : ℕ :=
  if bad then n - n%2 else 2

def fastSiteUpdate (m : ℕ) (nd nz v : ℤ) (oddBad evenBad : Bool)
    (s : ℤ × List ℤ) (a : ℕ) : ℤ × List ℤ :=
  let n := m-a
  let atom := fastSiteAtom m nd nz v oddBad evenBad a
  let odd := if 1 ≤ n then max s.1 (atom (oddExtreme n oddBad)) else s.1
  let score := if 2 ≤ n then max odd (atom (evenExtreme n evenBad)) else odd
  (score, if 0 < score then score::s.2 else s.2)

def uniformScore (m : ℕ) (nd nz v : ℤ) : ℤ :=
  (m : ℤ)-v+(if 0 < nd then 0 else min 0 nz)+4

def fastSiteValues (m : ℕ) (nd nz v : ℤ) (oddBad evenBad : Bool) : List ℤ :=
  if oddBad && evenBad then
    let score := uniformScore m nd nz v
    if 0 < score then List.replicate m score else []
  else
    ((List.range m).reverse.foldl (fastSiteUpdate m nd nz v oddBad evenBad) (0,[])).2

def fastSite (p d base t : ℤ) (oddBad evenBad : Bool) : List ℤ :=
  let count := fastCount p d base
  let m := siteMultiplicity d t
  let nd := 6*count (-25) 25 + 4*count (-17) 17 + 2*count (-16) 16 - (m : ℤ)
  let nz := 5*(count (-59) (-34) + count 34 59)
  let v := nz-nd+6*(50*d/p)+4*(34*d/p)+2*(32*d/p)-10*(25*d/p)
  fastSiteValues m nd nz v oddBad evenBad

def progressionLength (p a b : ℤ) : ℕ := ((b-a+p-1)/p).toNat

def emitRun (n : ℕ) (f : Unit → List ℤ) : List (ℕ × List ℤ) :=
  if n = 0 then [] else [(n,f ())]

/-- One weighted entry for the initial site, and up to three periodic runs. -/
def fastHalf (p d a : ℤ) : List (ℕ × List ℤ) :=
  let n := progressionLength p a (25*d)
  let init := min 1 n
  let n16 := max init (progressionLength p a (16*d))
  let n17 := max init (progressionLength p a (17*d))
  emitRun init (fun _ => fastSite p d a a (decide (0 < (34*d+a)/p))
    (decide ((34*d-a)/p ≠ (34*d+a)/p))) ++
  emitRun (n16-init) (fun _ => fastSite p d a 0 true true) ++
  emitRun (n17-n16) (fun _ => fastSite p d a (16*d) true true) ++
  emitRun (n-n17) (fun _ => fastSite p d a (17*d) true true)

def binKeys : List ℕ := (nrange 1 17).reverse

def fastClassBinsSpec (p d b : ℤ) : List (ℕ × ℕ) :=
  let runs := fastHalf p d b ++ fastHalf p d (p-b)
  binKeys.map fun w => (w, (runs.map fun (n, weights) => n * weights.count (w:ℤ)).sum)

def addSiteWeight (n : ℕ) (bins : List ℕ) (w : ℤ) : List ℕ :=
  if 0 < w ∧ w ≤ 16 then bins.modify (16-w.toNat) (·+n) else bins

def addSiteRun (bins : List ℕ) (run : ℕ × List ℤ) : List ℕ :=
  run.2.foldl (addSiteWeight run.1) bins

def fastClassBins (p d b : ℤ) : List (ℕ × ℕ) :=
  let runs := fastHalf p d b ++ fastHalf p d (p-b)
  binKeys.zip (runs.foldl addSiteRun (List.replicate 16 0))

def fastClasses (p d : ℤ) : List (ℤ × List (ℕ × ℕ)) :=
  let walls := increasingZ (0 :: (p/2) :: ([16,17,25,34,59] : List ℤ).map
    (fun e => let r := e*d%p; min r (p-r)))
  (adjacent walls).map fun (l,r) => (r-l, fastClassBins p d ((l+r)/2))

/-- In a run of equal weights, the eligible ranks form an initial segment. -/
def runPop (q : Option ℕ) (j start w n : ℕ) : ℕ :=
  if w < j then 0 else
    match q with
    | none => n
    | some q => min n (q+1+(w-j)/2-start)

def rankStep (q : Option ℕ) (j : ℕ) (s bin : ℕ × ℕ) : ℕ × ℕ :=
  if bin.2 = 0 then s else (s.1+bin.2,s.2+runPop q j s.1 bin.1 bin.2)

def fastPopulation (q : Option ℕ) (j : ℕ) (bins : List (ℕ × ℕ)) : ℕ :=
  (bins.foldl (rankStep q j) (0,0)).2

def fastMiddleNumerator (p d : ℤ) (q : Option ℕ) : ℤ :=
  let classes := fastClasses p d
  let charge := match q with
    | none => 0
    | some k => Sweep.rowCharge p d (80*d/p).toNat k
  charge + (binKeys.map fun j =>
    min (40*d) ((classes.map fun (qty, bins) => qty * (fastPopulation q j bins : ℤ)).sum)).sum

def fastMiddleCand (mid : ℚ) (q : Option ℕ) : ℚ :=
  let p := 4*mid.num
  let d := 4*(mid.den : ℤ)
  (fastMiddleNumerator p d q : ℚ)/(2000*d : ℤ)

def rowDen (r : ArithRow) : ℕ := r.left.den * r.right.den

def rowWidthNum (r : ArithRow) : ℤ :=
  r.right.num * (r.left.den:ℤ) - r.left.num * (r.right.den:ℤ)

def rowMidNum (r : ArithRow) : ℤ :=
  r.left.num * (r.right.den:ℤ) + r.right.num * (r.left.den:ℤ)

/-- The midpoint is reduced by integer gcd. -/
def fastMidpointParts (r : ArithRow) : ℤ × ℕ :=
  let num := rowMidNum r
  let den := 2 * rowDen r
  let g := den.gcd num.natAbs
  (num / (g:ℤ), den / g)

def fastMiddleRow (r : ArithRow) (q : Option ℕ) : Bool :=
  let (num,den) := fastMidpointParts r
  let p := 4*num
  let d := 4*(den:ℤ)
  decide (0 < rowWidthNum r ∧ 0 ≤ r.upper ∧ 0 < p ∧
    q.getD 0 ≤ (80*d/p).toNat ∧
    rowWidthNum r * fastMiddleNumerator p d q * bigUnit ≤ r.upper * (rowDen r : ℤ) * (2000*d))

def checkFastMiddle : List ArithRow → List (Option ℕ) → Bool
  | [], [] => true
  | r::rs, q::qs => fastMiddleRow r q && checkFastMiddle rs qs
  | _, _ => false

private theorem mem_orders (m a e : ℕ) :
    e ∈ nrange 1 (m-a+1) ↔ 0 < e ∧ e ≤ m-a := by
  simp only [nrange,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨e-1,by omega,by omega⟩

private theorem fold_max_le_iff (xs : List ℕ) (f : ℕ → ℤ) (b v : ℤ) :
    xs.foldl (fun s e => max s (f e)) b ≤ v ↔ b ≤ v ∧ ∀ e ∈ xs, f e ≤ v := by
  induction xs generalizing b with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨hb,he⟩,ht⟩
      exact ⟨hb, fun x hx => hx.elim (fun heq => heq ▸ he) (ht x)⟩
    · rintro ⟨hb,ht⟩
      exact ⟨⟨hb,ht e (.inl rfl)⟩,fun x hx => ht x (.inr hx)⟩

private theorem atom_le_odd {m a e : ℕ} {nd nz v : ℤ} {oddBad evenBad : Bool}
    (he : 0 < e ∧ e ≤ m-a) (ho : e%2=1) :
    fastSiteAtom m nd nz v oddBad evenBad a e ≤
      fastSiteAtom m nd nz v oddBad evenBad a (oddExtreme (m-a) oddBad) := by
  have hx : oddExtreme (m-a) oddBad % 2 = 1 := by cases oddBad <;> simp [oddExtreme] <;> omega
  simp only [fastSiteAtom,ho,hx,ite_true]
  cases oddBad <;> simp only [oddExtreme,Bool.false_eq_true,ite_false,ite_true,add_zero] <;>
    split_ifs <;> omega

private theorem atom_le_even {m a e : ℕ} {nd nz v : ℤ} {oddBad evenBad : Bool}
    (he : 0 < e ∧ e ≤ m-a) (ho : e%2≠1) :
    fastSiteAtom m nd nz v oddBad evenBad a e ≤
      fastSiteAtom m nd nz v oddBad evenBad a (evenExtreme (m-a) evenBad) := by
  have hx : evenExtreme (m-a) evenBad % 2 ≠ 1 := by cases evenBad <;> simp [evenExtreme] <;> omega
  simp only [fastSiteAtom,ho,hx,ite_false]
  cases evenBad <;> simp only [evenExtreme,Bool.false_eq_true,ite_false,ite_true,add_zero] <;>
    split_ifs <;> omega

private theorem fastSiteUpdate_eq (m : ℕ) (nd nz v : ℤ) (oddBad evenBad : Bool) :
    fastSiteUpdate m nd nz v oddBad evenBad =
      siteUpdate m (fastSiteAtom m nd nz v oddBad evenBad) := by
  funext s a
  let n := m-a
  let f := fastSiteAtom m nd nz v oddBad evenBad a
  let score := (nrange 1 (n+1)).foldl (fun x e => max x (f e)) s.1
  let odd := if 1 ≤ n then max s.1 (f (oddExtreme n oddBad)) else s.1
  let combined := if 2 ≤ n then max odd (f (evenExtreme n evenBad)) else odd
  have hsites := (fold_max_le_iff (nrange 1 (n+1)) f s.1 score).mp (le_refl score)
  have hodd : odd ≤ score := by
    dsimp only [odd]
    split_ifs with h
    · apply max_le hsites.1
      apply hsites.2
      apply (mem_orders m a _).mpr
      cases oddBad <;> simp [oddExtreme,n] at * <;> omega
    · exact hsites.1
  have hf : combined ≤ score := by
    dsimp only [combined]
    split_ifs with h
    · apply max_le hodd
      apply hsites.2
      apply (mem_orders m a _).mpr
      cases evenBad <;> simp [evenExtreme,n] at * <;> omega
    · exact hodd
  have hgodd : s.1 ≤ odd := by dsimp only [odd]; split_ifs <;> first | exact le_max_left _ _ | exact le_rfl
  have hg : odd ≤ combined := by dsimp only [combined]; split_ifs <;> first | exact le_max_left _ _ | exact le_rfl
  have hh : score ≤ combined := by
    apply (fold_max_le_iff _ _ _ _).mpr
    refine ⟨hgodd.trans hg,?_⟩
    intro e he
    have hn := (mem_orders m a e).mp he
    by_cases ho : e%2=1
    · apply (atom_le_odd hn ho).trans
      have h : 1 ≤ n := by dsimp only [n]; omega
      exact (show f (oddExtreme n oddBad) ≤ odd by simp [odd,h]).trans hg
    · apply (atom_le_even hn ho).trans
      have h : 2 ≤ n := by dsimp only [n]; omega
      change f (evenExtreme n evenBad) ≤ combined
      rw [show combined = max odd (f (evenExtreme n evenBad)) by simp only [combined,h,ite_true]]
      exact le_max_right _ _
  change (combined,if 0 < combined then combined::s.2 else s.2) =
    (score,if 0 < score then score::s.2 else s.2)
  rw [le_antisymm hf hh]

private theorem uniformAtom (m a : ℕ) (nd nz v : ℤ) (ha : a < m) :
    fastSiteAtom m nd nz v true true a (m-a) = uniformScore m nd nz v := by
  simp only [fastSiteAtom,ite_self,ite_true,uniformScore,show m-(m-a)-a=0 by omega,Nat.cast_zero]
  omega

private theorem uniformAtom_le (m a e : ℕ) (nd nz v : ℤ) (ha : a < m) (he : e ≤ m-a) :
    fastSiteAtom m nd nz v true true a e ≤ uniformScore m nd nz v := by
  simp only [fastSiteAtom,ite_self,ite_true,uniformScore]
  split_ifs <;> omega

private theorem uniformUpdate (m : ℕ) (nd nz v : ℤ) (s : ℤ×List ℤ) (a : ℕ) (ha : a < m) :
    fastSiteUpdate m nd nz v true true s a =
      let score := max s.1 (uniformScore m nd nz v)
      (score, if 0 < score then score::s.2 else s.2) := by
  rw [fastSiteUpdate_eq]
  unfold siteUpdate
  dsimp only
  have hh :
      (nrange 1 (m-a+1)).foldl (fun b e => max b (fastSiteAtom m nd nz v true true a e)) s.1 =
        max s.1 (uniformScore m nd nz v) := by
    apply le_antisymm
    · apply (fold_max_le_iff _ _ _ _).mpr
      exact ⟨le_max_left _ _,fun e he =>
        (uniformAtom_le m a e nd nz v ha ((mem_orders _ _ _).mp he).2).trans (le_max_right _ _)⟩
    · apply max_le
      · exact ((fold_max_le_iff _ _ _ _).mp le_rfl).1
      · rw [←uniformAtom m a nd nz v ha]
        exact ((fold_max_le_iff _ _ _ _).mp le_rfl).2 _ ((mem_orders _ _ _).mpr ⟨by omega, le_rfl⟩)
  rw [hh]

private theorem uniformFold (m : ℕ) (nd nz v : ℤ) (as : List ℕ) (s : ℤ×List ℤ)
    (has : ∀ a ∈ as, a < m)
    (hs : max s.1 (uniformScore m nd nz v) = max 0 (uniformScore m nd nz v)) :
    (as.foldl (fastSiteUpdate m nd nz v true true) s).2 =
      if 0 < uniformScore m nd nz v then (List.replicate as.length (uniformScore m nd nz v)) ++ s.2
      else s.2 := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons,uniformUpdate _ _ _ _ _ _ (has a List.mem_cons_self),ih]
    · simp only [hs,List.length_cons]
      by_cases h : 0 < uniformScore m nd nz v
      · have he : max 0 (uniformScore m nd nz v)=uniformScore m nd nz v := by omega
        simp [he,h,List.replicate_succ']
      · have he : max 0 (uniformScore m nd nz v)=0 := by omega
        simp [he,h]
    · intro b hb
      exact has b (List.mem_cons_of_mem _ hb)
    · simp only [hs]
      omega

private theorem fastSiteValues_eq (m : ℕ) (nd nz v : ℤ) (oddBad evenBad : Bool) :
    fastSiteValues m nd nz v oddBad evenBad =
      ((List.range m).reverse.foldl (fastSiteUpdate m nd nz v oddBad evenBad) (0,[])).2 := by
  cases oddBad <;> cases evenBad <;> simp only [fastSiteValues,Bool.false_and,Bool.true_and,
    Bool.false_eq_true,ite_false,ite_true]
  rw [uniformFold _ _ _ _ _ _ (fun a ha => List.mem_range.mp (List.mem_reverse.mp ha)) rfl]
  simp

theorem fastSite_self (p d t : ℤ) :
    fastSite p d t t (decide (0 < (34*d+t)/p)) (decide ((34*d-t)/p ≠ (34*d+t)/p)) =
      middleSite p d t := by
  unfold fastSite
  simp only [fastSiteValues_eq,fastSiteUpdate_eq,fastCount,siteMultiplicity]
  unfold middleSite siteUpdate fastSiteAtom
  simp only [Bool.ite_eq_true_distrib, decide_eq_true_eq]

private theorem fastCount_shift (p d a l r k : ℤ) (hp : p ≠ 0) :
    fastCount p d (a+k*p) l r = fastCount p d a l r := by
  unfold fastCount
  simp only [sub_add_eq_sub_sub,Int.sub_mul_ediv_right _ _ hp]
  omega

private theorem fastSite_later (p d a u : ℤ) (i : ℕ) (hp : 0 < p) (hd : 0 < d)
    (ha : 0 ≤ a) (hi : 0 < i) (hm : siteMultiplicity d (a+(i:ℤ)*p) = siteMultiplicity d u) :
    middleSite p d (a+(i:ℤ)*p) = fastSite p d a u true true := by
  let t := a+(i:ℤ)*p
  have hpt : p ≤ t := by
    dsimp only [t]
    have hprod := mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ (i:ℤ) by omega) hp.le
    omega
  have hr : 0 < (34*d+t)/p := by
    have hh : (1:ℤ) ≤ (34*d+t)/p := (Int.le_ediv_iff_mul_le hp).mpr (by omega)
    omega
  have hl : (34*d-t)/p ≠ (34*d+t)/p := by
    have hh := Int.ediv_le_ediv hp (show 34*d-t+1*p ≤ 34*d+t by omega)
    rw [Int.add_mul_ediv_right _ _ hp.ne'] at hh
    omega
  rw [← fastSite_self]
  change fastSite p d t t (decide (0 < (34*d+t)/p)) (decide ((34*d-t)/p ≠ (34*d+t)/p)) = _
  rw [decide_eq_true_eq.mpr hr,decide_eq_true_eq.mpr hl]
  simp only [fastSite,hm,t,fastCount_shift _ _ _ _ _ _ hp.ne']

private theorem progressionLength_mono {p a b c : ℤ} (hp : 0 < p) (hbc : b ≤ c) :
    progressionLength p a b ≤ progressionLength p a c := by
  by_contra! hn
  have hb := (middle_range_index a b p (progressionLength p a c) hp).mp hn
  have hc : progressionLength p a c < progressionLength p a c :=
    (middle_range_index a c p _ hp).mpr (hb.trans_le hbc)
  omega

def expandRuns (runs : List (ℕ × List ℤ)) : List ℤ :=
  runs.flatMap fun (n, ws) => (List.replicate n ws).flatten

private theorem expand_emit (n : ℕ) (f : Unit → List ℤ) :
    expandRuns (emitRun n f) = (List.replicate n (f ())).flatten := by
  cases n <;> simp [emitRun,expandRuns]

private theorem expand_append (xs ys : List (ℕ × List ℤ)) :
    expandRuns (xs++ys) = expandRuns xs ++ expandRuns ys := by
  simp [expandRuns]

private theorem segment_flatMap {a len : ℕ} {f : ℕ → List ℤ} {ws : List ℤ}
    (h : ∀ i ∈ List.range' a len, f i = ws) :
    (List.range' a len).flatMap f = (List.replicate len ws).flatten := by
  rw [List.flatMap_def,show (List.range' a len).map f = (List.range' a len).map (fun _ => ws)
    from List.map_congr_left h,List.map_const',List.length_range']

/-- The partition agrees with the original raw bag, including order and multiplicity. -/
theorem fastHalf_raw (p d a : ℤ) (hp : 0 < p) (hd : 0 < d) (ha : 0 ≤ a) :
    expandRuns (fastHalf p d a) = (iRange a (25*d) p).flatMap (middleSite p d) := by
  let n := progressionLength p a (25*d)
  let z := min 1 n
  let s := max z (progressionLength p a (16*d))
  let t := max z (progressionLength p a (17*d))
  let F := fun i : ℕ => middleSite p d (a+(i:ℤ)*p)
  have hzs : z ≤ s := le_max_left _ _
  have hst : s ≤ t := max_le_max le_rfl (progressionLength_mono hp (by omega))
  have htn : t ≤ n := max_le (min_le_right _ _) (progressionLength_mono hp (by omega))
  have hr : List.range n = ((List.range' 0 z ++ List.range' z (s-z)) ++
      List.range' s (t-s)) ++ List.range' t (n-t) := by
    rw [List.range_eq_range', show List.range' 0 z ++ List.range' z (s-z) = List.range' 0 s by
      simpa only [zero_add,Nat.add_sub_of_le hzs] using
        (List.range'_append_1 (s:=0) (m:=z) (n:=s-z))]
    rw [show List.range' 0 s ++ List.range' s (t-s) = List.range' 0 t by
      simpa only [zero_add,Nat.add_sub_of_le hst] using
        (List.range'_append_1 (s:=0) (m:=s) (n:=t-s))]
    simpa only [zero_add,Nat.add_sub_of_le htn] using
      (List.range'_append_1 (s:=0) (m:=t) (n:=n-t)).symm
  have hIndex (i : ℕ) (j : ℤ) : i < progressionLength p a j ↔ a+(i:ℤ)*p < j :=
    middle_range_index _ _ _ _ hp
  have hstart (i : ℕ) (hzi : z ≤ i) (hin : i < n) : 0 < i := by
    dsimp only [z] at hzi
    omega
  unfold iRange
  simp only [show ¬p ≤ 0 by omega,ite_false,List.flatMap_map]
  change expandRuns (fastHalf p d a) = (List.range n).flatMap F
  rw [hr]
  simp only [fastHalf, expand_append, expand_emit, List.flatMap_append]
  congr 1
  · congr 1
    · congr 1
      · symm
        apply segment_flatMap
        intro i hi
        have hij := List.mem_range'_1.mp hi
        have hi0 : i=0 := by dsimp only [z] at hij; omega
        subst i
        simpa [F] using (fastSite_self p d a).symm
      · symm
        apply segment_flatMap
        intro i hi
        obtain ⟨h₁,h₂⟩ := List.mem_range'_1.mp hi
        have his : i < s := by omega
        have hi16 : i < progressionLength p a (16*d) := by
          dsimp only [s] at his
          omega
        have h16 := (hIndex i (16*d)).mp hi16
        exact fastSite_later p d a 0 i hp hd ha (hstart i h₁ (by omega))
          (by simp [siteMultiplicity,h16,show a+(i:ℤ)*p < 17*d by omega,show 0<16*d by omega,
            show 0<17*d by omega])
    · symm
      apply segment_flatMap
      intro i hi
      obtain ⟨h₁,h₂⟩ := List.mem_range'_1.mp hi
      have hit : i < t := by omega
      have hi17 : i < progressionLength p a (17*d) := by
        dsimp only [t] at hit
        omega
      have h17 := (hIndex i (17*d)).mp hi17
      have h16 : ¬ a+(i:ℤ)*p < 16*d := by rw [←hIndex]; exact not_lt.mpr ((le_max_right _ _).trans h₁)
      exact fastSite_later p d a (16*d) i hp hd ha (hstart i (by omega) (by omega))
        (by simp [siteMultiplicity,h17,h16,show 16*d < 17*d by omega])
  · symm
    apply segment_flatMap
    intro i hi
    obtain ⟨h₁,h₂⟩ := List.mem_range'_1.mp hi
    have h17 : ¬ a+(i:ℤ)*p < 17*d := by rw [←hIndex]; exact not_lt.mpr ((le_max_right _ _).trans h₁)
    exact fastSite_later p d a (17*d) i hp hd ha (hstart i (by omega) (by omega))
      (by simp [siteMultiplicity,h17,show ¬ a+(i:ℤ)*p < 16*d by omega,show ¬17*d < 16*d by omega])

end OddZetaSix.B40a.Cert
