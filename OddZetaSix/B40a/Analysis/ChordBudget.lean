import OddZetaSix.B40a.Certificate.Generated.All

namespace OddZetaSix.B40a.Cert.Chord

abbrev Pt := ℚ × ℚ
def mag (z : Pt) := z.1^2 + z.2^2
def dist2 (z w : Pt) := mag (z.1-w.1, z.2-w.2)
def sqPt (z : Pt) : Pt := (z.1^2-z.2^2, 2*z.1*z.2)
def rootLo (q : ℚ) : ℚ := ((Nat.sqrt (qfloor (q*(coord:ℚ)^2)).toNat):ℚ)/coord

/-- Distance to the rectangle containing a translated panel. -/
def phaseD (z w : Pt) (p : ℤ) : ℚ :=
  let t := ((p:ℚ)-118)/100
  let x := max 0 (max (min (z.1+t) (w.1+t)) (-max (z.1+t) (w.1+t)))
  rootLo (x^2+z.2^2)

def cp (z w : Pt) (p k : ℤ) : ℤ := qceil ((fix:ℚ)*k.natAbs*dist2 z w/(2*phaseD z w p))
def center (c : Circle) : Pt := ((c.re:ℚ)/coord,(c.im:ℚ)/coord)
def radius (c : Circle) := (c.radius:ℚ)/coord
def circleD (z w : Pt) (c : Circle) :=
  max (radius c) (rootLo (min (dist2 (sqPt z) (center c)) (dist2 (sqPt w) (center c))))
def cc (z w : Pt) (c : Circle) : ℤ :=
  let d := circleD z w c
  qceil ((fix:ℚ)*c.mass/(2*massTotal)*(dist2 (sqPt z) (sqPt w)/(2*d^2)+dist2 z w/d))
def phSum (z w : Pt) := (phaseBlocks.map fun t=>cp z w t.1 t.2.2+cp z w t.2.1 t.2.2).sum
def cSum (z w : Pt) := ((allCircles circles).map (cc z w)).sum
def budget (p : Panel) : Prop :=
  let z := contourZ p.a
  let w := contourZ p.b
  0≤z.2 ∧ z.2<w.2 ∧ (phaseBlocks.all fun t=>decide (0<phaseD z w t.1 ∧ 0<phaseD z w t.2.1))=true ∧
  20*(max (endpoint lookup circles p.a) (endpoint lookup circles p.b))+
    5*phSum z w+8*cSum z w≤20*peak

instance (p : Panel) : Decidable (budget p) := by unfold budget; infer_instance
end OddZetaSix.B40a.Cert.Chord
