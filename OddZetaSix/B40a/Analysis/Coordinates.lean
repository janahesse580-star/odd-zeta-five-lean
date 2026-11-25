import OddZetaSix.B40a.Analysis.BendGeometry
noncomputable section
namespace OddZetaSix.B40a.Cert
def scaleN (n : ℕ) : ℝ := 50*(n:ℝ)

/-- The unshifted limiting coordinates of a finite contour point. -/
structure Coordinates (n : ℕ) (z : ℂ) (x y θ : ℝ) : Prop where
  real_eq : z.re+1=scaleN n*(x-118/100+θ)
  imag_eq : |z.im|=scaleN n*y
  x_low : 1≤x
  x_high : x≤2
  y_nonneg : 0≤y
  drift_low : 0≤θ
  drift_high : θ≤2/(scaleN n)

end OddZetaSix.B40a.Cert
