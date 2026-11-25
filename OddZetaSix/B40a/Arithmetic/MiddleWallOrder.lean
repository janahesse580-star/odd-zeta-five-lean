import OddZetaSix.B40a.Arithmetic.MiddleRowWallAudit

namespace OddZetaSix.B40a.Cert
open Set

def signedMiddleRadii : List ℤ := [-59,-34,-25,-17,-16,0,16,17,25,34,59]

private theorem signedRadii_gaps : signedMiddleRadii.all (fun e =>
    signedMiddleRadii.all (fun f => decide (e<f → (f-e).toNat∈middleFrequencies))) = true := by
  decide +kernel

private theorem row_pos {r : ArithRow} (hr : r∈middleRows) : 0<(r.left:ℝ) := by
  have h := List.all_eq_true.mp middleRows_freq r hr
  simp only [checkMiddleFrequencies,Bool.and_eq_true,decide_eq_true_eq] at h
  exact_mod_cast h.1.1

/-- On an open certificate row the frequency ratio is strictly above its
floor, even if it takes an integer value at one of the two endpoints. -/
theorem middle_floor_strict {r : ArithRow} (hr : r∈middleRows) {P : ℝ}
    (hP : P∈Ioo (r.left:ℝ) r.right) {k : ℕ} (hk : k∈middleFrequencies) :
    (middleFloor r k:ℝ)<(k:ℝ)/P := by
  let y := (P+(r.right:ℝ))/2
  have hPy : P<y := by dsimp [y]; linarith [hP.2]
  have hy : y∈Ioo (r.left:ℝ) r.right := ⟨hP.1.trans hPy,by dsimp [y]; linarith [hP.2]⟩
  have h0 : 0<P := (row_pos hr).trans hP.1
  have hk0 : 0<k := by
    change k∈List.filter _ _ at hk
    simpa using (List.mem_filter.mp hk).2
  have hlo := Int.floor_le ((k:ℝ)/y)
  rw [middleRows_floor hr hy hk] at hlo
  exact hlo.trans_lt (div_lt_div_of_pos_left (by exact_mod_cast hk0) h0 hPy)

/-- Order of any pair of distinct signed wall families, including arbitrary
period translates, throughout the interior of a certified row. -/
theorem middle_wall_order_iff {r : ArithRow} (hr : r∈middleRows) {P : ℝ}
    (hP : P∈Ioo (r.left:ℝ) r.right) {e f : ℤ} (he : e∈signedMiddleRadii)
    (hf : f∈signedMiddleRadii) (hef : e<f) (i j : ℤ) :
    (e:ℝ)+i*P < (f:ℝ)+j*P ↔ i-j≤middleFloor r (f-e).toNat := by
  have hh := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp signedRadii_gaps e he) f hf)
  have hk := hh hef
  let k := (f-e).toNat
  have hp : 0<P := (row_pos hr).trans hP.1
  have hcast : (k:ℝ)=(f:ℝ)-e := by
    have hz : (k:ℤ)=f-e := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hz
  have h₁ : (e:ℝ)+i*P < (f:ℝ)+j*P ↔ ((i-j:ℤ):ℝ)<(k:ℝ)/P := by
    rw [lt_div_iff₀ hp,hcast,Int.cast_sub,sub_mul]; constructor <;> intro h <;> linarith
  rw [h₁]
  constructor
  · intro h
    rw [←middleRows_floor hr hP hk]
    exact Int.le_floor.mpr h.le
  · intro h
    exact (show ((i-j:ℤ):ℝ)≤middleFloor r k by exact_mod_cast h).trans_lt
      (middle_floor_strict hr hP hk)

end OddZetaSix.B40a.Cert
