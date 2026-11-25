import OddZetaSix.SixFunctional
import OddZetaSix.Statement

noncomputable section
open Polynomial
open scoped BigOperators

namespace OddZetaSix.B40a

def fiveRank (n : ℕ) : ℕ := 40*n

def normalizer (n : ℕ) : ℝ := 2000*(n : ℝ)^2

def fiveWeights : Finset ℕ := {7,9,11,13,15}

def fiveValues (s : Fin 5) : ℝ := (riemannZeta ((7+2*s.val : ℕ) : ℂ)).re

def offsets : Fin 12 → ℕ := ![0,0,0,0,0,0,8,8,8,8,9,9]

def center (n : ℕ) : ℕ := 59*n+1

def numerator (n : ℕ) : ℚ[X] :=
  (X + C (center n : ℚ)) *
    (rising 1 (25*n) * rising (93*(n : ℚ)+2) (25*n))^5

def denominator (n : ℕ) : ℚ[X] :=
  ∏ b : Fin 12, rising (((34+offsets b)*n+1 : ℕ) : ℚ) ((50-2*offsets b)*n+1)

def normalization (n : ℕ) : ℚ :=
  2*(∏ b : Fin 12, (((50-2*offsets b)*n).factorial : ℚ)) /
    ((25*n).factorial : ℚ)^10

def entryKernel (n i j : ℕ) (x : ℝ) : ℝ :=
  (normalization n : ℝ) * (numerator n).eval₂ (Rat.castHom ℝ) x /
    (denominator n).eval₂ (Rat.castHom ℝ) x *
    (evenBasis i).eval₂ (Rat.castHom ℝ) (x+center n) *
    (evenBasis j).eval₂ (Rat.castHom ℝ) (x+center n)

def fiveFunctional (n : ℕ) : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) ℝ :=
  fun i j => ∑' v : ℕ, iteratedDeriv 4 (entryKernel n i j) ((v : ℝ)-25*(n : ℝ))/24

def FiveZetaIrrational : Prop :=
  ∃ s ∈ fiveWeights, Irrational ((riemannZeta (s : ℂ)).re)

theorem fiveWeights_index (i : Fin 5) : 7+2*i.val ∈ fiveWeights := by
  fin_cases i <;> norm_num [fiveWeights]

end OddZetaSix.B40a
