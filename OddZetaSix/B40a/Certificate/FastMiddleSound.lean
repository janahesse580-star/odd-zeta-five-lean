import OddZetaSix.B40a.Certificate.FastMiddle
import OddZetaSix.B40a.Arithmetic.MiddleSweepMinimum
import OddZetaSix.B40a.Arithmetic.MiddleStripGrid
import OddZetaSix.B40a.Arithmetic.CertificateRows

namespace OddZetaSix.B40a.Cert
open Finset Sweep

def expandBins (bins : List (ℕ × ℕ)) : List ℤ :=
  bins.flatMap fun (w,n) => List.replicate n (w:ℤ)

private theorem expandRuns_count (rs : List (ℕ × List ℤ)) (w : ℤ) :
    (expandRuns rs).count w = (rs.map fun (n,ws) => n * ws.count w).sum := by
  simp only [expandRuns,List.count_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  obtain ⟨n,ws⟩ := x
  simp [List.count_flatten]

private theorem binKeys_range (w : ℕ) : w ∈ binKeys ↔ 0 < w ∧ w < 17 := by
  simp only [binKeys,nrange,List.mem_reverse,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨w-1,by omega,by omega⟩

private theorem addSiteWeight_length (n : ℕ) (bins : List ℕ) (w : ℤ) :
    (addSiteWeight n bins w).length = bins.length := by
  unfold addSiteWeight
  split_ifs <;> simp

private theorem addSiteWeights_length (ws : List ℤ) (n : ℕ) (bins : List ℕ) :
    (ws.foldl (addSiteWeight n) bins).length = bins.length := by
  induction ws generalizing bins with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons,ih,addSiteWeight_length]

private theorem addSiteRuns_length (rs : List (ℕ × List ℤ)) (bins : List ℕ) :
    (rs.foldl addSiteRun bins).length = bins.length := by
  induction rs generalizing bins with
  | nil => rfl
  | cons r rs ih => simp only [List.foldl_cons,ih,addSiteRun,addSiteWeights_length]

private theorem addSiteWeight_count (n i : ℕ) (bins : List ℕ) (w : ℤ)
    (hi : i < bins.length) (hi16 : i < 16) :
    (addSiteWeight n bins w)[i]! = bins[i]! + if w = ((16-i:ℕ):ℤ) then n else 0 := by
  unfold addSiteWeight
  by_cases h : 0 < w ∧ w ≤ 16
  · rw [ite_eq_left h]
    have ht : i < (bins.modify (16-w.toNat) (·+n)).length := by simpa using hi
    rw [getElem!_pos (bins.modify (16-w.toNat) (·+n)) i ht,List.getElem_modify,getElem!_pos bins i hi]
    split_ifs <;> omega
  · have hn : w ≠ ((16-i:ℕ):ℤ) := by omega
    simp only [h,hn,ite_false,Nat.add_zero]

private theorem addSiteWeights_count (ws : List ℤ) (n i : ℕ) (bins : List ℕ)
    (hi : i < bins.length) (hi16 : i < 16) :
    (ws.foldl (addSiteWeight n) bins)[i]! = bins[i]! + n * ws.count ((16-i:ℕ):ℤ) := by
  induction ws generalizing bins with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (by rwa [addSiteWeight_length]),addSiteWeight_count _ _ _ _ hi hi16]
    simp only [List.count_cons,beq_iff_eq]
    split_ifs <;> simp_all only [Nat.mul_add,Nat.mul_one,Nat.add_zero] <;> omega

private theorem addSiteRuns_count (rs : List (ℕ × List ℤ)) (i : ℕ) (bins : List ℕ)
    (hi : i < bins.length) (hi16 : i < 16) :
    (rs.foldl addSiteRun bins)[i]! =
      bins[i]! + (rs.map fun (n,ws) => n * ws.count ((16-i:ℕ):ℤ)).sum := by
  induction rs generalizing bins with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,addSiteRun]
    rw [ih _ (by rwa [addSiteWeights_length]),addSiteWeights_count _ _ _ _ hi hi16,Nat.add_assoc]

private theorem binKeys_size : binKeys.length = 16 := by decide

private theorem binKeys_get (i : ℕ) (hi : i < binKeys.length) :
    binKeys[i] = 16-i := by
  have hi16 : i < 16 := by simpa only [binKeys_size] using hi
  change ((List.range' 1 16).reverse)[i]'(by simpa using hi16) = _
  simp [List.getElem_reverse]
  omega

theorem fastClassBins_eq_spec (p d b : ℤ) : fastClassBins p d b = fastClassBinsSpec p d b := by
  unfold fastClassBins fastClassBinsSpec
  dsimp only
  let runs := fastHalf p d b ++ fastHalf p d (p-b)
  let bins := runs.foldl addSiteRun (List.replicate 16 0)
  have hz : bins.length = 16 := by simp [bins,addSiteRuns_length]
  change binKeys.zip bins = binKeys.map (fun w => (w,(runs.map fun (n,ws) => n*ws.count (w:ℤ)).sum))
  apply List.ext_getElem
  · simp [binKeys_size,hz]
  · intro i hi h'
    have hi16 : i < 16 := by simpa [binKeys_size,hz] using hi
    have hget := addSiteRuns_count runs i (List.replicate 16 0) (by simpa using hi16) hi16
    rw [getElem!_pos (List.replicate 16 (0:ℕ)) i (by simpa using hi16)] at hget
    have hn : i < bins.length := by rwa [hz]
    rw [List.getElem_zip,List.getElem_map,binKeys_get]
    simp only [List.getElem_replicate,zero_add] at hget
    change bins[i]! = _ at hget
    rw [getElem!_pos bins i hn] at hget
    rw [hget]

/-- The 16 bins expand to the exact sorted original bag. -/
theorem fastClass_expand (p d b : ℤ) (hp : 0 < p) (hd : 0 < d) (hb : 0 ≤ b) (hp' : b ≤ p) :
    expandBins (fastClassBins p d b) =
      middleSortedSlots ((middleClassSites p d b).flatMap (middleSite p d)) := by
  let xs := (middleClassSites p d b).flatMap (middleSite p d)
  have hraw : expandRuns (fastHalf p d b ++ fastHalf p d (p-b)) = xs := by
    simp only [expandRuns,List.flatMap_append] at *
    change expandRuns (fastHalf p d b) ++ expandRuns (fastHalf p d (p-b)) = xs
    rw [fastHalf_raw _ _ _ hp hd hb,fastHalf_raw _ _ _ hp hd (by omega)]
    simp only [xs,middleClassSites,List.flatMap_append]
  simp only [expandBins,fastClassBins_eq_spec,fastClassBinsSpec,List.flatMap_map,←expandRuns_count,hraw,middleSortedSlots]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro w hw
  obtain ⟨h₁,h₂⟩ := (binKeys_range _).mp hw
  have H := middleUpdateHist_bin xs (Array.replicate 17 0) h₁ (by simpa using h₂)
  rw [getElem!_pos (Array.replicate 17 (0:ℕ)) w
    (by simpa using h₂ : w < (Array.replicate 17 (0:ℕ)).size)] at H
  simpa [xs,List.flatMap_def] using congrArg (fun n => List.replicate n (w:ℤ)) H.symm

private theorem classBin_keys (p d b : ℤ) (x : ℕ × ℕ) (hx : x ∈ fastClassBins p d b) :
    x.1 ≤ 16 := by
  rw [fastClassBins_eq_spec] at hx
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
  have := (binKeys_range w).mp hw
  omega

private theorem expanded_keys (bins : List (ℕ × ℕ)) (h : ∀ x ∈ bins, x.1 ≤ 16) :
    ∀ w ∈ expandBins bins, w ≤ 16 := by
  intro w hw
  obtain ⟨⟨b,n⟩,hx,hm⟩ := List.mem_flatMap.mp hw
  obtain rfl := List.eq_of_mem_replicate hm
  exact_mod_cast h (b,n) hx

private theorem wallBounds (p d z : ℤ) (hp : 0 < p)
    (hz : z ∈ StripGrid.walls p d) : 0 ≤ z ∧ z ≤ p := by
  have h := ((StripGrid.increasing_spec _).2.2 _).mp hz
  simp only [List.mem_cons,List.mem_map] at h
  rcases h with rfl|rfl|⟨e,_,rfl⟩
  · omega
  · omega
  · unfold StripGrid.foldAddr
    have hl := Int.emod_nonneg (e*d) hp.ne'
    have hr := Int.emod_lt_of_pos (e*d) hp
    omega

private theorem expandClasses (p d : ℤ) (hp : 0 < p) (hd : 0 < d) :
    (fastClasses p d).map (fun (qty,bins) => (qty,(expandBins bins).toArray)) =
      middleClasses p d := by
  rw [middleClasses_eq_sorted]
  change ((adjacent (StripGrid.walls p d)).map _).map _ = (adjacent (StripGrid.walls p d)).map _
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨l,r⟩ h
  have hab := StripGrid.adjacent_gap _ (StripGrid.increasing_spec _).1 h
  have hl := wallBounds p d l hp hab.1
  have hr := wallBounds p d r hp hab.2.1
  simp only [Function.comp_apply]
  rw [fastClass_expand p d ((l+r)/2) hp hd (by omega) (by omega)]

private def rankWeight (q : Option ℕ) (rank : ℕ) (w : ℤ) : ℤ :=
  match q with
  | none => w
  | some k => w-2*((rank-k:ℕ):ℤ)

private def rankSum (q : Option ℕ) (j start : ℕ) (ws : List ℤ) : ℤ :=
  ∑ i ∈ range ws.length, eligible j (rankWeight q (start+i) ws[i]!)

private theorem rankSum_split (q : Option ℕ) (j start : ℕ) (xs ys : List ℤ) :
    rankSum q j start (xs++ys) = rankSum q j start xs + rankSum q j (start+xs.length) ys := by
  unfold rankSum
  rw [List.length_append,Finset.sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro i hi
    have ht := mem_range.mp hi
    have ht' : i < (xs++ys).length := by simp; omega
    rw [getElem!_pos (xs++ys) i ht',List.getElem_append_left ht,getElem!_pos xs i ht]
  · apply sum_congr rfl
    intro i hi
    have ht := mem_range.mp hi
    have ht' : xs.length+i < (xs++ys).length := by simp; omega
    have hElem : (xs++ys)[xs.length+i] = ys[i] := by
      rw [List.getElem_append_right (by omega)]
      simp
    rw [getElem!_pos (xs++ys) (xs.length+i) ht',getElem!_pos ys i ht,hElem,add_assoc]

private theorem sum_cut (n k : ℕ) :
    (∑ i ∈ range n, if i < k then (1:ℤ) else 0) = (min n k : ℕ) := by
  rw [← Finset.sum_filter]
  have h : (range n).filter (fun i => i < k) = range (min n k) := by
    ext i
    simp
  rw [h]
  simp

private theorem rankSum_run (q : Option ℕ) (j start w n : ℕ) (hw : w ≤ 16) :
    rankSum q j start (List.replicate n (w:ℤ)) = (runPop q j start w n : ℤ) := by
  unfold rankSum
  simp only [List.length_replicate]
  have hv : ∀ i ∈ range n, (List.replicate n (w:ℤ))[i]! = (w:ℤ) := by
    intro i hi
    have ht : i < (List.replicate n (w:ℤ)).length := by simpa using mem_range.mp hi
    rw [getElem!_pos (List.replicate n (w:ℤ)) i ht,List.getElem_replicate]
  have hsum :
      (∑ i ∈ range n, eligible j (rankWeight q (start+i) (List.replicate n (w:ℤ))[i]!)) =
      ∑ i ∈ range n, eligible j (rankWeight q (start+i) (w:ℤ)) := by
    apply sum_congr rfl
    intro i hi
    rw [hv i hi]
  rw [hsum]
  unfold runPop
  by_cases h : w < j
  · rw [ite_eq_left h,Nat.cast_zero]
    apply sum_eq_zero
    intro i _
    cases q <;> simp only [rankWeight,eligible] <;> split_ifs <;> omega
  · rw [ite_eq_right h]
    cases q with
    | none =>
      have h' : (j:ℤ) ≤ (w:ℤ) ∧ (w:ℤ) ≤ 16 := by omega
      simp [rankWeight,eligible,h']
    | some k =>
      rw [← sum_cut n (k+1+(w-j)/2-start)]
      apply sum_congr rfl
      intro i _
      have he : ((j:ℤ) ≤ (w:ℤ)-2*((start+i-k:ℕ):ℤ) ∧
        (w:ℤ)-2*((start+i-k:ℕ):ℤ) ≤ 16) ↔ i < k+1+(w-j)/2-start := by omega
      simp only [rankWeight,eligible,he]

private theorem rankSum_bins (q : Option ℕ) (j : ℕ) (bins : List (ℕ×ℕ))
    (h : ∀ x ∈ bins, x.1 ≤ 16) (start total : ℕ) :
    ((bins.foldl (rankStep q j) (start,total)).2 : ℤ) =
      (total:ℤ)+rankSum q j start (expandBins bins) := by
  induction bins generalizing start total with
  | nil => simp [expandBins,rankSum]
  | cons x xs ih =>
    rcases x with ⟨w,n⟩
    have hw := h (w,n) List.mem_cons_self
    have ht : ∀ x ∈ xs, x.1 ≤ 16 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hn : n = 0
    · subst n
      simpa only [List.foldl_cons,rankStep,ite_true,expandBins,List.flatMap_cons,List.replicate_zero,
        List.nil_append] using ih ht start total
    · simp only [List.foldl_cons,rankStep,hn,ite_false,expandBins,List.flatMap_cons]
      rw [ih ht,rankSum_split,rankSum_run _ _ _ _ _ hw,List.length_replicate,Nat.cast_add,add_assoc]
      rfl

private theorem fastPop_sound (p d b : ℤ) (q : Option ℕ) (j : ℕ) :
    (fastPopulation q j (fastClassBins p d b) : ℤ) =
      rankSum q j 0 (expandBins (fastClassBins p d b)) := by
  simpa only [fastPopulation,Nat.cast_zero,zero_add] using
    rankSum_bins q j (fastClassBins p d b) (classBin_keys p d b) 0 0

private theorem fastNumerator_eq (p d : ℤ) (q : Option ℕ) (hp : 0 < p) (hd : 0 < d) :
    fastMiddleNumerator p d q =
      match q with
      | none => cappedLayers d (book ((middleClasses p d).flatMap allAt) blank)
      | some k => score (middleClasses p d) p d (80*d/p).toNat k := by
  let cs := fastClasses p d
  let arrayClass : (ℤ × List (ℕ × ℕ)) → (ℤ × Array ℤ) :=
    fun (qty,bins) => (qty,(expandBins bins).toArray)
  have hkeys (f : ℕ→ℤ) : (binKeys.map f).sum = ∑ j ∈ Ico 1 17,f j := by
    simp only [binKeys,List.map_reverse,List.sum_reverse,Sweep.nrangeSum]
  have hall : ∀ c ∈ cs, ∃ a b : ℤ, c=(a,fastClassBins p d b) := by
    intro c h
    obtain ⟨⟨l,r⟩,_,rfl⟩ := List.mem_map.mp h
    exact ⟨r-l,(l+r)/2,rfl⟩
  have hval : ∀ B ∈ cs.map arrayClass, ∀ r < B.2.size, B.2[r]! ≤ 16 := by
    intro B hB r hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hB
    obtain ⟨a,b,rfl⟩ := hall c hc
    have hn : r < (expandBins (fastClassBins p d b)).length := by simpa [arrayClass] using hr
    simp only [arrayClass,List.getElem!_toArray,getElem!_pos (expandBins (fastClassBins p d b)) r hn]
    exact expanded_keys _ (classBin_keys p d b) _ (List.getElem_mem hn)
  have H (j : ℕ) :
      (cs.map (fun (qty,bins) => qty * (fastPopulation q j bins : ℤ))).sum =
        ((cs.map arrayClass).map (fun B => B.1 * rankSum q j 0 B.2.toList)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    obtain ⟨a,b,rfl⟩ := hall c hc
    simp [arrayClass,fastPop_sound]
  simp only [fastMiddleNumerator,hkeys]
  rw [← expandClasses p d hp hd]
  change _ = match q with
    | none => cappedLayers d (book ((cs.map arrayClass).flatMap allAt) blank)
    | some k => score (cs.map arrayClass) p d (80*d/p).toNat k
  cases q with
  | none =>
    rw [zero_add,book_cap]
    apply sum_congr rfl
    intro j _
    rw [H,level_flatMap]
    simp only [allAt_level,rankSum,rankWeight,Array.length_toList,Array.getElem!_toList]
  | some k =>
    change _ = rowCharge p d (80*d/p).toNat k +
      cappedLayers d (book (folded (cs.map arrayClass) k) blank)
    rw [book_cap]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [H,folded_population _ _ _ (by have := mem_Ico.mp hj; omega) hval]
    simp only [rankSum,rankWeight,Array.length_toList,Array.getElem!_toList,zero_add,population,adjusted]

private theorem min_fold_le_init {α : Type} (xs : List α) (f : α → ℤ) (b : ℤ) :
    xs.foldl (fun s x => min s (f x)) b ≤ b := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih _).trans (min_le_left _ _)

private theorem min_fold_le_choice {α : Type} (xs : List α) (f : α → ℤ) (b : ℤ)
    (x : α) (h : x∈xs) : xs.foldl (fun s y => min s (f y)) b ≤ f x := by
  induction xs generalizing b with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact (min_fold_le_init ys f _).trans (min_le_right _ _)
    · exact ih _ h

/-- Only one legitimate candidate is needed to bound the original minimum. -/
theorem middleValue_le_fastMiddleCand (mid : ℚ) (q : Option ℕ) (hp : 0 < mid.num)
    (hq : q.getD 0 ≤ (80*(4*(mid.den:ℤ))/(4*mid.num)).toNat) :
    middleValue mid ≤ fastMiddleCand mid q := by
  rw [middleValue_eq_best]
  unfold fastMiddleCand
  dsimp only
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Int.cast_le.mpr
  have hd : 0 < (mid.den : ℤ) := by exact_mod_cast mid.den_pos
  rw [fastNumerator_eq _ _ _ (by omega) (by omega)]
  cases q with
  | none => exact min_fold_le_init _ _ _
  | some k =>
    apply min_fold_le_choice
    exact List.mem_range.mpr (by simp only [Option.getD_some] at hq; omega)

private theorem mid_as_mkRat (r : ArithRow) :
    (r.left+r.right)/2 = mkRat (rowMidNum r) (2*rowDen r) := by
  have hb : (r.left.den : ℚ) ≠ 0 := by exact_mod_cast r.left.den_nz
  have he : (r.right.den : ℚ) ≠ 0 := by exact_mod_cast r.right.den_nz
  calc
    (r.left+r.right)/2 =
        ((r.left.num:ℚ)/r.left.den + (r.right.num:ℚ)/r.right.den)/2 := by
          simp only [Rat.num_div_den]
    _ = _ := by
      rw [Rat.mkRat_eq_div]
      push_cast [rowMidNum,rowDen]
      field_simp

private theorem midpointParts_sound (r : ArithRow) :
    fastMidpointParts r = (((r.left+r.right)/2).num,((r.left+r.right)/2).den) := by
  have hz : 2*rowDen r ≠ 0 := by
    exact Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.mul_pos r.left.den_pos r.right.den_pos))
  simp only [fastMidpointParts,mid_as_mkRat,Rat.num_mkRat,Rat.den_mkRat,hz,ite_false]

private theorem rowWidth_sound (r : ArithRow) :
    r.right-r.left = (rowWidthNum r : ℚ)/(rowDen r : ℚ) := by
  have hb : (r.left.den : ℚ) ≠ 0 := by exact_mod_cast r.left.den_nz
  have he : (r.right.den : ℚ) ≠ 0 := by exact_mod_cast r.right.den_nz
  calc
    r.right-r.left = (r.right.num:ℚ)/r.right.den - (r.left.num:ℚ)/r.left.den := by
      simp only [Rat.num_div_den]
    _ = _ := by
      push_cast [rowWidthNum,rowDen]
      field_simp

theorem fastMiddleRow_sound (r : ArithRow) (q : Option ℕ) (h : fastMiddleRow r q = true) :
    rowValue false r ≤ (r.upper : ℚ)/bigUnit := by
  let mid := (r.left+r.right)/2
  let p := 4*mid.num
  let d := 4*(mid.den:ℤ)
  let w := rowWidthNum r
  let den := rowDen r
  have hd : (0:ℚ) < (2000*d:ℤ) := by
    have := mid.den_pos
    push_cast [d]
    positivity
  have hd' : (0:ℚ) < (den:ℚ) := by
    have hd0 : 0 < den := Nat.mul_pos r.left.den_pos r.right.den_pos
    exact_mod_cast hd0
  have hu : (0:ℚ) < (bigUnit:ℚ) := by norm_num [bigUnit]
  have hh :
      0 < w ∧ 0 ≤ r.upper ∧ 0 < p ∧ q.getD 0 ≤ (80*d/p).toNat ∧
        w * fastMiddleNumerator p d q * bigUnit ≤ r.upper * (den:ℤ) * (2000*d) := by
    simpa only [fastMiddleRow,midpointParts_sound,decide_eq_true_eq] using h
  have hp : 0 < mid.num := by have := hh.2.2.1; dsimp only [p] at this; omega
  have hw : (0:ℚ) ≤ r.right-r.left := by
    rw [rowWidth_sound]
    exact div_nonneg (by exact_mod_cast hh.1.le) hd'.le
  unfold rowValue
  simp only [Bool.false_eq_true,ite_false]
  apply (mul_le_mul_of_nonneg_left (middleValue_le_fastMiddleCand mid q hp hh.2.2.2.1) hw).trans
  change (r.right-r.left) * ((fastMiddleNumerator p d q : ℚ)/(2000*d:ℤ)) ≤
    (r.upper:ℚ)/bigUnit
  rw [rowWidth_sound,div_mul_div_comm]
  apply (le_div_iff₀ hu).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos hd' hd)).mpr
  push_cast
  have hx := (Int.cast_le (R:=ℚ)).mpr hh.2.2.2.2
  push_cast at hx
  simpa only [w,den,mul_assoc] using hx

theorem checkedFastMiddle_sum_bound (rs : List ArithRow) (qs : List (Option ℕ))
    (h : checkFastMiddle rs qs = true) :
    (rs.map (rowValue false)).sum ≤ (arithTotal rs : ℚ)/bigUnit := by
  induction rs generalizing qs with
  | nil => simp [arithTotal]
  | cons r rs ih =>
    cases qs with
    | nil => simp [checkFastMiddle] at h
    | cons q qs =>
      simp only [checkFastMiddle,Bool.and_eq_true] at h
      have hb := add_le_add (fastMiddleRow_sound r q h.1) (ih qs h.2)
      simpa only [arithTotal,List.map_cons,List.sum_cons,Int.cast_add,add_div] using hb

theorem checkFastMiddle_append {rs ts : List ArithRow} {qs us : List (Option ℕ)}
    (h : checkFastMiddle rs qs = true) (h' : checkFastMiddle ts us = true) :
    checkFastMiddle (rs++ts) (qs++us) = true := by
  induction rs generalizing qs with
  | nil =>
    cases qs with
    | nil => exact h'
    | cons q qs => simp [checkFastMiddle] at h
  | cons r rs ih =>
    cases qs with
    | nil => simp [checkFastMiddle] at h
    | cons q qs =>
      simp only [checkFastMiddle,Bool.and_eq_true] at h
      simp only [List.cons_append,checkFastMiddle,h.1,ih h.2,Bool.and_self]

#print axioms fastClass_expand
#print axioms middleValue_le_fastMiddleCand
#print axioms fastMiddleRow_sound

end OddZetaSix.B40a.Cert
