import OddZetaSix.B40a.Analysis.LogIntervals

noncomputable section
namespace OddZetaSix.B40a.Cert
open Real

/-- Sound fixed-point interval at scale fix. -/
def Encloses (i : Interval) (x : ℝ) := (i.lo:ℝ)≤(fix:ℝ)*x ∧ (fix:ℝ)*x≤(i.hi:ℝ)
theorem Encloses.add {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (plus a b) (x+y) := by
  unfold Encloses plus at *
  push_cast
  rw [mul_add]
  exact ⟨add_le_add ha.1 hb.1,add_le_add ha.2 hb.2⟩

theorem floor_bound (q : ℚ) : (qfloor q:ℝ)≤q := by
  rw [qfloor_eq_floor,←Rat.floor_cast (α:=ℝ)]
  exact Int.floor_le _
theorem ceil_bound (q : ℚ) : (q:ℝ)≤qceil q := by
  rw [qceil_eq_ceil,←Rat.ceil_cast (α:=ℝ)]
  exact Int.le_ceil _

theorem Encloses.mul_rat {a : Interval} {x : ℝ} (ha : Encloses a x) (q : ℚ) :
    Encloses (scale a q) ((q:ℝ)*x) := by
  obtain ⟨l,u⟩ := ha
  have lo (z : ℤ) := floor_bound ((z:ℚ)*q)
  have hi (z : ℤ) := ceil_bound ((z:ℚ)*q)
  push_cast at lo hi
  unfold Encloses scale
  split_ifs with h
  · have hR : (q:ℝ)≤0 := by exact_mod_cast h.le
    exact ⟨(lo _).trans (by linarith only [mul_le_mul_of_nonpos_right u hR]),
      (by linarith only [mul_le_mul_of_nonpos_right l hR] : (fix:ℝ)*(q*x)≤a.lo*q) |>.trans (hi _)⟩
  · have hR : (0:ℝ)≤q := by exact_mod_cast le_of_not_gt h
    exact ⟨(lo _).trans (by linarith only [mul_le_mul_of_nonneg_right l hR]),
      (by linarith only [mul_le_mul_of_nonneg_right u hR] : (fix:ℝ)*(q*x)≤a.hi*q) |>.trans (hi _)⟩

theorem pow2q_zpow (e : ℤ) : pow2q e=(2:ℚ)^e := by
  cases e with
  | ofNat n => simp [pow2q]
  | negSucc n => simp [pow2q,one_div,zpow_negSucc]

theorem logRat_sound (q : ℚ) (hq : 0<q) : Encloses (logRat q) (Real.log (q:ℝ)) := by
  let A := q.num.natAbs.log2
  let B := q.den.log2
  let e₀ : ℤ := (A:ℤ)-B
  let e := if q<pow2q e₀ then e₀-1 else e₀
  have hnum := Rat.num_pos.mpr hq
  have npos : q.num.natAbs≠0 := Int.natAbs_ne_zero.mpr hnum.ne'
  have lowN : (2:ℚ)^A≤q.num := by
    have H : ((2^A:ℕ):ℤ)≤q.num := by
      rw [←Int.natAbs_of_nonneg hnum.le]
      exact_mod_cast Nat.log2_self_le npos
    exact_mod_cast H
  have hiD : (q.den:ℚ)<2^B*2 := by
    have H := Nat.lt_log2_self (n:=q.den)
    rw [pow_succ] at H
    exact_mod_cast H
  have dpos : (0:ℚ)<q.den := by exact_mod_cast q.den_pos
  have eqQ : q=(q.num:ℚ)/q.den := by exact (Rat.num_div_den q).symm
  have hbase : pow2q (e₀-1) ≤ q := by
    rw [pow2q_zpow,eqQ,le_div_iff₀ dpos]
    simp only [e₀,zpow_sub₀ (by norm_num : (2:ℚ)≠0),zpow_natCast,zpow_one]
    have hT : (0:ℚ)<2^B := by positivity
    calc
      (2^A/2^B/2:ℚ)*q.den ≤ (2^A/2^B/2:ℚ)*(2^B*2) := mul_le_mul_of_nonneg_left hiD.le (by positivity)
      _ = 2^A := by field_simp
      _ ≤ _ := lowN
  have hle : pow2q e≤q := by unfold e; split <;> first | assumption | exact le_of_not_gt (by assumption)
  have hp : 0<pow2q e := by rw [pow2q_zpow]; positivity
  have hm : 1≤q/pow2q e := (one_le_div hp).mpr hle
  have H := (Encloses.mul_rat (show Encloses lnTwo (Real.log 2) from by
    simpa only [Encloses,lnTwo,Rat.cast_ofNat] using atanhLog_sound 2 (by norm_num)) (e:ℚ)).add (atanhLog_sound _ hm)
  change Encloses (plus (scale lnTwo (e:ℚ)) (atanhLog (q/pow2q e))) _
  convert H using 1
  rw [Rat.cast_div,Real.log_div (by exact_mod_cast hq.ne') (by exact_mod_cast hp.ne'),
    pow2q_zpow,Rat.cast_zpow,Real.log_zpow]
  push_cast; ring

end OddZetaSix.B40a.Cert

noncomputable section
namespace OddZetaSix.B40a.Cert

theorem node_sound (t : Lookup) (ht : checkLookup t=true) (i : ℕ) (hi : i<129) :
    Encloses t.nodes[i]! (Real.log ((128+(i:ℝ))/128)) := by
  simp only [checkLookup,Bool.and_eq_true] at ht
  have h := List.all_eq_true.mp ht.1.2 i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  have H := atanhLog_sound ((128+(i:ℚ))/128) (by
    have nn : 0 ≤ (i:ℚ) := by positivity
    linarith)
  simpa only [logNode,Encloses,h.1,h.2,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat] using H

theorem shift_sound (t : Lookup) (ht : checkLookup t=true) (e : ℕ) (he : e<80) :
    Encloses t.shifts[e]! ((e:ℝ)*Real.log 2-2*Real.log coord) := by
  simp only [checkLookup,Bool.and_eq_true] at ht
  have h := List.all_eq_true.mp ht.2 e (List.mem_range.mpr he)
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  have H := (Encloses.mul_rat (show Encloses lnTwo (Real.log 2) from by
    simpa only [lnTwo,Encloses,Rat.cast_ofNat] using atanhLog_sound 2 (by norm_num)) (e:ℚ)).add
    ((logRat_sound (coord:ℚ) (by norm_num [coord])).mul_rat (-2))
  simpa only [Encloses,h.1,h.2,logShift,Rat.cast_natCast,Rat.cast_neg,Rat.cast_ofNat,Rat.cast_intCast,
    neg_mul,←sub_eq_add_neg] using H

/-- The lookup's tangent upper bound and its lower slope at the next grid node.
The grid residual is less than one cell (128 equal units per dyadic octave). -/
theorem squaredLog_sound (t : Lookup) (ht : checkLookup t=true) (D : ℤ) (hD : 0<D)
    (hsize : D.toNat.log2<80) :
    (squaredLog t D false:ℝ)≤(fix:ℝ)*Real.log ((D:ℝ)/(coord:ℝ)^2) ∧
    (fix:ℝ)*Real.log ((D:ℝ)/(coord:ℝ)^2)≤(squaredLog t D true:ℝ) := by
  let e := D.toNat.log2
  let p : ℤ := 2^e
  let k := D*128/p
  let l := D*128-k*p
  have hp : 0<p := by dsimp [p]; positivity
  have Dnat : (D.toNat:ℤ)=D := Int.toNat_of_nonneg hD.le
  have h0 : 2^e≤D.toNat := Nat.log2_self_le (by omega)
  have h1 : D.toNat<2^e*2 := by simpa only [e,pow_succ] using (Nat.lt_log2_self (n:=D.toNat))
  have hpD : p≤D := by unfold p; rw [←Dnat]; exact_mod_cast h0
  have hDp : D<2*p := by unfold p; rw [mul_comm,←Dnat]; exact_mod_cast h1
  have kl : 128≤k := (Int.le_ediv_iff_mul_le hp).mpr (by linarith)
  have ku : k<256 := (Int.ediv_lt_iff_lt_mul hp).mpr (by linarith)
  have ll := Int.ediv_mul_le (D*128) hp.ne'
  have lh := Int.lt_ediv_add_one_mul_self (D*128) hp
  change k*p≤_ at ll; change _<(k+1)*p at lh
  have hL : 0≤l := sub_nonneg.mpr ll
  have hP : l<p := by unfold l; linarith
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hDR : (0:ℝ)<D := by exact_mod_cast hD
  have hLR : (0:ℝ)≤l := by exact_mod_cast hL
  have hd2 : 0<(k+1)*p := Int.mul_pos (by omega) hp
  have hd1 : 0<k*p := Int.mul_pos (by omega) hp
  have heq : (D:ℝ)*128=(k:ℝ)*p+l := by dsimp [l]; push_cast; ring
  have ih : ((k-128).toNat:ℤ)=k-128 := Int.toNat_of_nonneg (by omega)
  have hr := node_sound t ht (k-128).toNat (by omega)
  have ecast : (128+((k-128).toNat:ℝ))/128=(k:ℝ)/128 := by
    have : (((k-128).toNat:ℕ):ℝ)=(k:ℝ)-128 := by exact_mod_cast ih
    rw [this]; ring
  rw [ecast] at hr
  have sh := shift_sound t ht e hsize
  let x := ((D:ℝ)*128)/((k:ℝ)*p)
  have hx : 0<x := by dsimp [x]; positivity
  have lt0 : ((k:ℝ)+1)*p>0 := by positivity
  have hu := Real.log_le_sub_one_of_pos hx
  have hl := Real.one_sub_inv_le_log_of_pos hx
  have upper : Real.log x≤(l:ℝ)/(k*p) := by
    apply hu.trans_eq; dsimp [x]; field_simp; linarith only [heq]
  have lower : (l:ℝ)/(((k:ℝ)+1)*p)≤Real.log x := by
    apply le_trans _ hl
    have ld : (D:ℝ)*128≤((k:ℝ)+1)*p := by exact_mod_cast lh.le
    calc _ ≤ (l:ℝ)/((D:ℝ)*128) := div_le_div_of_nonneg_left hLR (by positivity) ld
         _ = _ := by dsimp [x]; field_simp; linarith only [heq]
  have cc : (0:ℝ)<coord := by norm_num [coord]
  have xeq : ((D:ℝ)/(coord:ℝ)^2)=(k/128)*((p:ℝ)/(coord:ℝ)^2)*x := by
    dsimp [x]; field_simp <;> ring
  have logEq : Real.log ((D:ℝ)/(coord:ℝ)^2) =
      Real.log ((k:ℝ)/128)+((e:ℝ)*Real.log 2-2*Real.log coord)+Real.log x := by
    rw [xeq,Real.log_mul (by positivity) hx.ne',Real.log_mul (by positivity) (by positivity),
      Real.log_div hpR.ne' (by positivity),Real.log_pow,show (p:ℝ)=(2:ℝ)^e by simp [p],Real.log_pow]
    norm_num
  have hB : (0:ℝ)≤fix := by norm_num [fix]
  have flo (a b : ℤ) (hb : 0<b) : ((a/b:ℤ):ℝ)≤(a:ℝ)/b := by
    apply (le_div_iff₀ (by exact_mod_cast hb)).mpr
    exact_mod_cast Int.ediv_mul_le a hb.ne'
  have L := flo (fix*l) ((k+1)*p) hd2
  have U := flo (-fix*l) (k*p) hd1
  push_cast at L U
  have fL := mul_le_mul_of_nonneg_left lower hB
  have fU := mul_le_mul_of_nonneg_left upper hB
  rw [←mul_div_assoc] at fL fU
  have U' : ((-fix*l/(k*p):ℤ):ℝ)≤ -((fix:ℝ)*l/(k*p)) := U.trans_eq (by ring)
  unfold Encloses at hr sh
  change (((t.nodes[(k-128).toNat]!).lo+(t.shifts[e]!).lo+fix*l/((k+1)*p):ℤ):ℝ)≤_ ∧
    _≤(((t.nodes[(k-128).toNat]!).hi+(t.shifts[e]!).hi+ -(-fix*l/((k+0)*p)):ℤ):ℝ)
  push_cast only [Int.cast_add,Int.cast_neg]
  rw [add_zero,logEq]
  simp only [mul_add]
  exact ⟨add_le_add (add_le_add hr.1 sh.1) (L.trans fL),
    add_le_add (add_le_add hr.2 sh.2) (fU.trans (by linarith only [U']))⟩
end OddZetaSix.B40a.Cert
