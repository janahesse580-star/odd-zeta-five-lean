import OddZetaSix.B40a.Analysis.VandermondeEnergy
import OddZetaSix.B40a.Analysis.RateReduction
import OddZetaSix.B40a.Certificate.Generated.Witness

/-! Actual 34 reflected pairs, with masses on the probability scale. -/
noncomputable section
namespace OddZetaSix.B40a.Witness
open Finset Cert Orbit
def entries := allCircles circles
abbrev Index := Fin entries.length
def entry (k : Index) := entries.get k
def u (k : Index) : ℂ := (((entry k).re:ℝ)/(coord:ℝ):ℝ) +
  (((entry k).im:ℝ)/(coord:ℝ):ℝ)*Complex.I
def r (k : Index) : ℝ := ((entry k).radius:ℝ)/coord
def b (k : Index) : ℝ := ((entry k).mass:ℝ)/(2*massTotal)

private theorem geometry : entries.all (fun c=>decide (0<c.radius ∧ 0<c.mass))=true ∧
    (entries.map Circle.mass).sum=2000 ∧ entries.length=68 := by decide +kernel

theorem valid (i : Index) : 0<r i ∧ 0≤b i := by
  have H := of_decide_eq_true (List.all_eq_true.mp geometry.1 _ (List.get_mem entries i))
  change 0<(entry i).radius ∧ 0<(entry i).mass at H
  exact ⟨div_pos (by exact_mod_cast H.1) (by norm_num [coord]),
    div_nonneg (by exact_mod_cast H.2.le) (by norm_num [massTotal])⟩

theorem mass : ∑ i,b i=1 := by
  have hv : (∑ i : Index,(entry i).mass)=(entries.map Circle.mass).sum := by
    rw [←List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map entries Circle.mass)
  rw [geometry.2.1] at hv
  have hR : ∑ i : Index,((entry i).mass:ℝ)=2000 := by exact_mod_cast hv
  simp only [b,←sum_div,hR,massTotal]
  norm_num

def potential (z : ℂ) := ∑ k,b k*circlePotential (u k) (r k) z
def energy := ∑ k,∑ l,b k*b l*interaction (u k) (u l) (r k) (r l)
def errorSlope := ∑ k,b k/r k

theorem vandermonde {h : ℕ} (z : Fin h→ℂ) {ε : ℝ} (hε : 0<ε) :
    ‖(Matrix.vandermonde z).det^2‖ ≤ Real.exp
      (2*h*(∑ i,potential (z i)) + 2*(h:ℝ)^2*ε*errorSlope - (h:ℝ)^2*energy-h*Real.log ε) := by
  have hm : (∑ k,(h:ℝ)*b k)=h := by rw [←mul_sum,mass,mul_one]
  have H := vandermonde_witness_bound z u r (fun k=>(h:ℝ)*b k)
    (fun k=>(valid k).1) (fun k=>mul_nonneg (by positivity) (valid k).2) hm hε
  apply H.trans_eq
  congr 1
  have cross (i : Fin h) : (∑ k,(h:ℝ)*b k*(circlePotential (u k) (r k) (z i)+ε/r k)) =
      (h:ℝ)*potential (z i)+(h:ℝ)*ε*errorSlope := by
    unfold potential errorSlope
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl; intro k _; ring
  have eng : (∑ k,∑ l,(h:ℝ)*b k*(h*b l)*interaction (u k) (u l) (r k) (r l))=(h:ℝ)^2*energy := by
    unfold energy
    rw [mul_sum]; apply sum_congr rfl; intro k _
    rw [mul_sum]; apply sum_congr rfl; intro l _; ring
  simp_rw [cross,eng,sum_add_distrib,←mul_sum]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- Substitution into the actual contour integrand, including its edge Jacobians. -/
theorem integrand_bound (n : ℕ) (q : ℝ) (a : Fin (fiveRank n)→BendParam) {ε : ℝ} (hε : 0<ε) :
    let h : ℝ := fiveRank n
    ‖bendVandermondeIntegrand n q a‖ ≤ Real.exp
      (2*h*(∑ i,potential (bendScaledSquare n q (a i)))+2*h^2*ε*errorSlope-h^2*energy-h*Real.log ε)
      *∏ i,‖bendWeight n q (a i)‖ := by
  simp only [bendVandermondeIntegrand,norm_mul,Complex.norm_prod]
  exact mul_le_mul_of_nonneg_right (vandermonde _ hε) (prod_nonneg fun _ _=>norm_nonneg _)

end OddZetaSix.B40a.Witness
