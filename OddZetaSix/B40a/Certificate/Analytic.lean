import OddZetaSix.B40a.Certificate.FixedPoint

namespace OddZetaSix.B40a.Cert

structure Circle where
  re : ℤ
  im : ℤ
  radius : ℤ
  mass : ℤ

def scaleCircle (c : Circle) : Circle :=
  ⟨c.re*1000,c.im*1000,c.radius*1000,c.mass⟩

def reflectCircle (c : Circle) : Circle := ⟨c.re,-c.im,c.radius,c.mass⟩

def allCircles (cs : List Circle) : List Circle :=
  cs.flatMap fun c => let d := scaleCircle c; [d, reflectCircle d]

def circleOK (c : Circle) : Bool :=
  decide (0<c.im ∧ 0<c.radius ∧ 0<c.mass ∧
    c.re^2+c.im^2≤9*circUnits^2 ∧ c.radius≤circUnits)

def circleEnergyRow (t : Lookup) (cs : List Circle) (raw : Circle) : ℤ :=
  let a := scaleCircle raw
  (cs.map fun raw' =>
    let b := scaleCircle raw'
    let re := (a.re-b.re)^2
    let same := if a.re=b.re ∧ a.im=b.im then a.radius^2 else re+(a.im-b.im)^2
    let opp := re+(a.im+b.im)^2
    a.mass*b.mass*(squaredLog t same false+squaredLog t opp false)).sum

def knots : List (ℤ × ℤ) :=
  [(0,1700),(2500,2200),(5000,1000),(10000,-2000),(20000,-8100),
    (35000,-16300),(55000,-25700),(85000,-45500),(400000,-45500)]

def contourZ (tick : ℤ) : ℚ × ℚ :=
  let ((a,c),(b,d)) :=
    ((adjacent knots).find? (fun (u,v) => decide (u.1 ≤ tick ∧ tick ≤ v.1))).getD ((0,0),(1,0))
  let value : ℚ := (c : ℚ) + qfrac ((d-c)*(tick-a)) (b-a).toNat
  (118/100 - value/phaseTicks,(tick : ℚ)/phaseTicks)

def phaseBlocks : List (ℤ × ℤ × ℤ) :=
  [(0,50,5),(186,236,5),(68,168,-6),(84,152,-4),(86,150,-2)]

def phasePrimitive (x y : ℚ) : Interval :=
  let angle := if y=0 then scale piBounds (if 0<x then 1/2 else -1/2)
    else atanBounds (x/y)
  plus (plus (scale (logRat (x*x+y*y)) (x/2)) ⟨qfloor (-x*fix),qceil (-x*fix)⟩)
    (scale angle y)

def phaseUpper (tick : ℤ) : ℤ :=
  let (x,y) := contourZ tick
  let bias := scale piBounds (-2*y)
  ((phaseBlocks.foldl (fun s (a,b,m) =>
    let w : ℚ := qfrac (b-a) 100
    let width := scale (plus (logRat w) ⟨-fix,-fix⟩) (-w)
    let p := plus (phasePrimitive (x+qfrac (b-118) 100) y)
      (scale (phasePrimitive (x+qfrac (a-118) 100) y) (-1))
    plus s (scale (plus p width) (m : ℚ))) bias)).hi

structure Box where
  xlo : ℤ
  xhi : ℤ
  ylo : ℤ
  yhi : ℤ

def rect (x y : ℚ) : Box :=
  ⟨qfloor (coord*x),qceil (coord*x),qfloor (coord*y),qceil (coord*y)⟩

def squareBox (x y : ℚ) : Box := rect (x*x-y*y) (2*x*y)

def ceilSqrt (x : ℚ) : ℤ :=
  let r : ℤ := Nat.sqrt (qfloor x).toNat
  if (r : ℚ)^2=x then r else r+1

def maxDistSq (b : Box) (x y : ℤ) : ℤ :=
  (max (b.xlo-x).natAbs (b.xhi-x).natAbs : ℤ)^2 +
    (max (b.ylo-y).natAbs (b.yhi-y).natAbs : ℤ)^2

def minDist (b : Box) (x y : ℤ) : ℤ :=
  Nat.sqrt ((max (max (b.xlo-x) (x-b.xhi)) 0)^2 +
    (max (max (b.ylo-y) (y-b.yhi)) 0)^2).toNat

def iceil (a b : ℤ) : ℤ := -((-a)/b)

def endpoint (t : Lookup) (cs : List Circle) (y : ℤ) : ℤ :=
  let (x,v) := contourZ y
  let box := squareBox x v
  let total := ((allCircles cs).map fun c =>
    c.mass*squaredLog t (max (c.radius^2) (maxDistSq box c.re c.im)) true).sum
  phaseUpper y+iceil (2*total) (5*massTotal)

def panelUpper (t : Lookup) (cs : List Circle) (a b : ℤ) : ℤ :=
  let (x,y) := contourZ a
  let (u,v) := contourZ b
  let d := v-y
  let deriv2 := 1+((u-x)/d)^2
  let vel := ceilSqrt (4*deriv2*max (x*x+y*y) (u*u+v*v)*(coord : ℚ)^2)
  let zvel := ceilSqrt (deriv2 * (coord : ℚ)^2)
  let acc := qceil (2*deriv2*coord)
  let excursion := qceil ((vel : ℚ)*d/2)
  let zexc := qceil ((zvel : ℚ)*d/2)
  let xx := (x+u)/2
  let yy := (y+v)/2
  let box := squareBox xx yy
  let sp := ((allCircles cs).map fun c =>
    let dist := max c.radius (minDist box c.re c.im-excursion)
    c.mass*iceil (1000*(acc*dist+vel^2)) (dist^2)).sum
  let curv (p m : ℤ) :=
    let bb := rect (xx+qfrac (p-118) 100) yy
    let dist := max (coord/100) (max (qfloor (coord*y)) (minDist bb 0 0-zexc))
    qceil ((m.natAbs : ℚ)*deriv2*coord*1000/dist)
  let curvPhase := (phaseBlocks.map fun (l,r,m) => curv l m+curv r m).sum
  let total := curvPhase + iceil (4*sp) (5*massTotal)
  max (endpoint t cs a) (endpoint t cs b) + qceil (total*d^2*fix/(8*1000))

structure Panel where
  a : ℤ
  b : ℤ

def checkPanel (t : Lookup) (cs : List Circle) (maxValue : ℤ) (p : Panel) : Bool :=
  decide (p.a < p.b ∧ 0 ≤ p.a ∧ p.b ≤ 400000) &&
  !(knots.any fun v => decide (p.a < v.1 ∧ v.1 < p.b)) &&
  decide (panelUpper t cs p.a p.b ≤ maxValue)

def tailUpper : ℤ :=
  let init := [scale (logRat (5/4)) 5,scale (logRat (7/5)) (8/5),
    scale (logRat 4) (-9/5),scale piBounds (-8)].foldl plus ⟨0,0⟩
  ((phaseBlocks.foldl (fun s (a,b,m) =>
    let w : ℚ := qfrac (b-a) 100
    plus s (scale (plus (logRat w) ⟨-fix,-fix⟩) (-(m : ℚ)*w))) init)).hi

def numericalA (peak energy : ℤ) : ℚ :=
  let prefactor := (4/5 : ℚ) * ((plus ⟨3*fix,3*fix⟩ (scale (logRat (8/5)) (-2))).hi : ℚ) / fix
  prefactor+(peak : ℚ)/fix-(4/5 : ℚ)*((energy : ℚ)/(4*(massTotal : ℚ)^2*fix))

def panelChain (a b : ℤ) : List Panel → Bool
  | [] => decide (a=b)
  | p::ps => decide (a=p.a) && panelChain p.b b ps

end OddZetaSix.B40a.Cert
