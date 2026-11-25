import OddZetaSix.B40a.Analysis.Vertical
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-! The eight-node contour and the pole-free domains used for its deformation. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

def bendHeight : Fin 8 → ℝ := ![0, 1/40, 1/20, 1/10, 1/5, 7/20, 11/20, 17/20]
def bendC : Fin 8 → ℝ := ![17/1000, 22/1000, 10/1000, -20/1000, -81/1000, -163/1000, -257/1000, -455/1000]

def contourSide (upper : Bool) : ℝ := if upper then 1 else -1

def pointAt (upper : Bool) (x y : ℝ) : ℂ :=
  (x : ℂ) + ((contourSide upper * y : ℝ) : ℂ)*Complex.I

@[simp] theorem pointAt_re (s : Bool) (x y : ℝ) : (pointAt s x y).re = x := by
  simp [pointAt]

@[simp] theorem pointAt_im (s : Bool) (x y : ℝ) : (pointAt s x y).im = contourSide s*y := by
  simp [pointAt]

def bendNodeX (n : ℕ) (k : Fin 8) : ℝ :=
  contourAbscissa n + 50*(n : ℝ)*(17/1000-bendC k)

def bendNodeY (n : ℕ) (k : Fin 8) : ℝ := 50*(n : ℝ)*bendHeight k

def bendNode (n : ℕ) (s : Bool) (k : Fin 8) : ℂ :=
  pointAt s (bendNodeX n k) (bendNodeY n k)

theorem bendNode_zero (n : ℕ) (s : Bool) : bendNode n s 0 = contourPoint n 0 := by
  simp [bendNode,pointAt,bendNodeY,bendNodeX,bendHeight,bendC,contourPoint,
    Matrix.cons_val_zero]

theorem bendNode_height_nonneg (n : ℕ) (k : Fin 8) : 0 ≤ bendNodeY n k := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  fin_cases k <;> norm_num [bendNodeY,bendHeight,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> positivity

theorem bendNode_offset_le (n : ℕ) (k : Fin 8) :
    |bendNodeX n k - contourAbscissa n| ≤ 2*bendNodeY n k := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [bendNodeX,add_sub_cancel_left,abs_le]
  fin_cases k <;>
    norm_num [bendNodeY,bendHeight,bendC,Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
    constructor <;> linarith

theorem bendNode_x_in_halfplane (n : ℕ) (k : Fin 8) :
    -(34*(n : ℝ)+1) < bendNodeX n k := by
  have ha : (anchor n : ℝ) ≤ (n : ℝ) := by exact_mod_cast anchor_le n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  fin_cases k <;>
    norm_num [bendNodeX,contourAbscissa,bendC,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> linarith

def bendDomain (n : ℕ) (s : Bool) : Set ℂ :=
  {z | -(34*(n : ℝ)+1) < z.re ∧
    |z.re-contourAbscissa n| < 1/2 + 2*contourSide s*z.im}

theorem isOpen_bendDomain (n : ℕ) (s : Bool) : IsOpen (bendDomain n s) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const continuous_re
  · exact isOpen_lt (continuous_re.sub continuous_const).abs
      (continuous_const.add (continuous_const.mul continuous_im))

theorem convex_bendDomain (n : ℕ) (s : Bool) : Convex ℝ (bendDomain n s) := by
  intro z hz w hw a b ha hb hab
  change -(34*(n : ℝ)+1) < _ ∧ _ at hz hw ⊢
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul, abs_lt] at hz hw ⊢
  constructor
  · rcases eq_or_lt_of_le ha with h | h <;> rcases eq_or_lt_of_le hb with h' | h' <;>
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hz.1.le),mul_nonneg hb (sub_nonneg.mpr hw.1.le)]
  · constructor <;> rcases eq_or_lt_of_le ha with h | h <;>
      rcases eq_or_lt_of_le hb with h' | h' <;>
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hz.2.1.le),
        mul_nonneg hb (sub_nonneg.mpr hw.2.1.le),
        mul_nonneg ha (sub_nonneg.mpr hz.2.2.le),
        mul_nonneg hb (sub_nonneg.mpr hw.2.2.le)]

theorem sin_ne_zero_on_bendDomain (n : ℕ) (s : Bool) (z : ℂ)
    (hz : z ∈ bendDomain n s) : Complex.sin ((Real.pi : ℂ)*z) ≠ 0 := by
  intro h
  obtain ⟨m,hm⟩ := Complex.sin_eq_zero_iff.mp h
  have he : z = (m : ℂ) := by
    apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
    simpa only [mul_comm] using hm
  rw [he] at hz
  have hh := hz.2
  simp only [Complex.intCast_im,Complex.intCast_re,mul_zero,add_zero,contourAbscissa,abs_lt] at hh
  have hlo : (-(anchor n : ℝ)-1) < (m : ℝ) := by linarith
  have hhi : (m : ℝ) < -(anchor n : ℝ) := by linarith
  have hlo' : (-(anchor n : ℤ)-1) < m := by exact_mod_cast hlo
  have hhi' : m < -(anchor n : ℤ) := by exact_mod_cast hhi
  omega

theorem pointAt_mem_bendDomain (n : ℕ) (s : Bool) (x y : ℝ)
    (hx : -(34*(n : ℝ)+1)<x) (hy : |x-contourAbscissa n| ≤ 2*y) :
    pointAt s x y ∈ bendDomain n s := by
  change _ ∧ _
  simp only [pointAt_re,pointAt_im]
  refine ⟨hx,?_⟩
  cases s <;> norm_num [contourSide] <;> linarith

theorem bendNode_mem (n : ℕ) (s : Bool) (k : Fin 8) : bendNode n s k ∈ bendDomain n s :=
  pointAt_mem_bendDomain n s _ _ (bendNode_x_in_halfplane n k) (bendNode_offset_le n k)

theorem exists_bend_primitive (n i j : ℕ) (s : Bool) :
    ∃ F : ℂ → ℂ, ∀ z ∈ bendDomain n s,
      HasDerivAt F (contourIntegrand n i j z) z := by
  have hd : DifferentiableOn ℂ (contourIntegrand n i j) (bendDomain n s) := by
    intro z hz
    exact (contourIntegrand_analyticAt n i j z hz.1
      (sin_ne_zero_on_bendDomain n s z hz)).differentiableAt.differentiableWithinAt
  obtain ⟨F,hF⟩ := (convex_bendDomain n s).exists_forall_hasDerivWithinAt hd
  exact ⟨F,fun z hz => (hF z hz).hasDerivAt ((isOpen_bendDomain n s).mem_nhds hz)⟩

end OddZetaSix.B40a
