import Mathlib.Data.Rat.Defs

namespace OddZetaSix.B40a.Cert

def qfloor (q : ℚ) : ℤ := q.num / (q.den : ℤ)

def qceil (q : ℚ) : ℤ := -qfloor (-q)

def qfrac (a : ℤ) (b : Nat) : ℚ := (a : ℚ) / (b : ℚ)

def bigUnit : ℤ := 10^12

structure ArithRow where
  left : ℚ
  right : ℚ
  upper : ℤ

def nrange (a b : Nat) : List Nat := (List.range (b-a)).map (a+·)

def iRange (a b d : ℤ) : List ℤ :=
  if d ≤ 0 then [] else (List.range ((b-a+d-1)/d).toNat).map (fun (i : Nat) => a + (i : ℤ)*d)

def insertZ (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x<y then x::y::ys else if x=y then y::ys else y::insertZ x ys

def increasingZ (xs : List ℤ) : List ℤ := xs.foldl (fun s x => insertZ x s) []

def adjacent {α : Type} (xs : List α) : List (α × α) := xs.zip xs.tail

def middleSite (p d t : ℤ) : List ℤ :=
  let count (a b : ℤ) : ℤ := (b*d-t)/p - (a*d-t)/p
  let m : Nat := 6 + (if t<17*d then 4 else 0) + (if t<16*d then 2 else 0)
  let nd := 6*count (-25) 25 + 4*count (-17) 17 + 2*count (-16) 16 - (m : ℤ)
  let nz := 5*(count (-59) (-34) + count 34 59)
  let v := nz-nd+6*(50*d/p)+4*(34*d/p)+2*(32*d/p)-10*(25*d/p)
  let l := (34*d-t)/p
  let r := (34*d+t)/p
  let result := (List.range m).reverse.foldl (fun (s : ℤ × List ℤ) a =>
    let score := (nrange 1 (m-a+1)).foldl (fun prev e =>
      let order := (m-e-a : Nat)
      let inc := if 0 < nd then (order : ℤ) else min (order : ℤ) nz
      let bad := if e%2=1 then 0<r else l≠r
      max prev ((a : ℤ)-v+inc+(if bad then (e : ℤ)+4 else 0))) s.1
    (score, if 0<score then score::s.2 else s.2)) (0,[])
  result.2

def middleClasses (p d : ℤ) : List (ℤ × Array ℤ) :=
  let walls := increasingZ (0 :: (p/2) :: ([16,17,25,34,59] : List ℤ).map
    (fun e => let r := e*d%p; min r (p-r)))
  (adjacent walls).map fun (l,r) =>
    let b := (l+r)/2
    let sites := iRange b (25*d) p ++ iRange (p-b) (25*d) p
    let raw := sites.flatMap (middleSite p d)
    let hist := raw.foldl (fun (h : Array Nat) v => h.modify v.toNat (·+1))
      (Array.replicate 17 0)
    let sorted := (nrange 1 17).reverse.flatMap (fun (k : Nat) => List.replicate hist[k]! (k : ℤ))
    (r-l,sorted.toArray)

def bump (xs : Array ℤ) (w : ℤ) (qty : ℤ) : Array ℤ :=
  xs.modify w.toNat (· + qty)

def cappedLayers (d : ℤ) (h : Array ℤ) : ℤ :=
  ((nrange 1 17).reverse.foldl (fun (s : ℤ × ℤ) j =>
    let avail := s.1 + h[j]!
    (avail, s.2 + min (40*d) avail)) (0,0)).2

def middleValue (mid : ℚ) : ℚ :=
  let p := 4*mid.num
  let d : ℤ := 4*(mid.den : ℤ)
  let classes := middleClasses p d
  let blank : Array ℤ := Array.replicate 17 0
  let unfolded := classes.foldl (fun h (qty,bag) =>
    bag.foldl (fun h w => bump h w qty) h) blank
  let qmax := (80*d/p).toNat
  let result := (List.range (qmax+1)).foldl (fun (s : Array ℤ × ℤ) q =>
    let prior := classes.foldl (fun h (qty,bag) =>
      if q<bag.size then bump h bag[q]! qty else h) s.1
    let hist := classes.foldl (fun h (qty,bag) =>
      (nrange (q+1) (min (q+8) bag.size)).foldl (fun acc j =>
        let w := bag[j]! - 2*((j-q : Nat) : ℤ)
        if 0<w then bump acc w qty else acc) h) prior
    let line := (qmax-q : Nat)
    let row := 80*d*(line : ℤ) - p*(((qmax+q+1)*line/2 : Nat) : ℤ)
    (prior, min s.2 (row + cappedLayers d hist))) (blank, cappedLayers d unfolded)
  (result.2 : ℚ) / (2000*d : ℤ)

def periodEnds : List ℤ := [-59,-34,-25,-17,-16,0,16,17,25,34,59]

def periodScores (mid : ℚ) : ℚ × ℚ :=
  let n := mid.num
  let d : ℤ := mid.den
  let edges := increasingZ (0::d::periodEnds.map (fun x => (x*n)%d))
  let sums := (adjacent edges).foldl (fun (s : ℤ × ℤ) (a,b) =>
    let k := a+b
    let cnt (l r : ℤ) := (2*r*n-k)/(2*d) - (2*l*n-k)/(2*d) - ((r-l)*n)/d
    let score := max 0 (4+6*cnt (-25) 25+4*cnt (-17) 17+2*cnt (-16) 16
      -5*cnt (-59) (-34)-5*cnt 34 59)
    (s.1+(b-a)*score,s.2+(b-a)*((score-1)^2/4))) (0,0)
  ((sums.1 : ℚ)/d,(sums.2 : ℚ)/d)

def roundUp (q : ℚ) : ℚ := ((qceil (q*bigUnit) : ℤ) : ℚ)/bigUnit

def reciprocalSum (a : ℚ) (k : Nat) : ℚ :=
  let start := if 9/11 ≤ a then 1 else 2
  (((nrange start 17).map (fun (j : Nat) => roundUp (1/((j : ℚ)+a)^k))).sum) +
    roundUp (1/((k-1 : Nat) * (16+a)^(k-1)))

def smallValue (a b : ℚ) : ℚ :=
  let (f,g) := periodScores ((a+b)/2)
  (reciprocalSum a 2*f+reciprocalSum a 3*(f+g)/80)/50

def checkArithRow (small : Bool) (r : ArithRow) : Bool :=
  decide (r.left < r.right ∧ 0 ≤ r.upper) &&
  let v := if small then smallValue r.left r.right else middleValue ((r.left+r.right)/2)
  decide (qceil ((r.right-r.left)*v*bigUnit) = r.upper)

def arithTotal (rs : List ArithRow) : ℤ := (rs.map ArithRow.upper).sum

def arithChain (a b : ℚ) : List ArithRow → Bool
  | [] => decide (a=b)
  | r::rs => decide (a=r.left) && arithChain r.right b rs

def tailCapacity (p : ℚ) (l : ℕ) : ℚ :=
  max 0 (51-p)*((List.range 10).filter (fun j => decide (l≤14-2*j))).length +
  (84-max 76 (25+p))*((List.range 6).filter (fun j => decide (l≤10-2*j))).length

def clippedCell (a b : ℚ) (l : ℕ) : ℚ :=
  let fa := tailCapacity a l
  let fb := tailCapacity b l
  let corners := if (fa-40)*(fb-40)<0 then [a,a+(b-a)*(40-fa)/(fb-fa),b] else [a,b]
  ((adjacent corners).map fun (x,y) =>
    (y-x)*(min 40 (tailCapacity x l)+min 40 (tailCapacity y l))/2).sum

def highTail : ℚ :=
  ((nrange 1 15).map (fun l => clippedCell 50 51 l + clippedCell 51 59 l)).sum/2000 + 9/40

end OddZetaSix.B40a.Cert
