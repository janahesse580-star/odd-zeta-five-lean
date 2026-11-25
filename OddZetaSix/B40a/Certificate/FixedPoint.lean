import OddZetaSix.B40a.Certificate.Arithmetic
import Mathlib.Data.Nat.Sqrt

namespace OddZetaSix.B40a.Cert

def fix : ℤ := 10^9
def coord : ℤ := 10^6
def phaseTicks : ℚ := 100000
def circUnits : ℤ := 1000
def massTotal : ℤ := 1000

structure Interval where
  lo : ℤ
  hi : ℤ

def plus (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩

def scale (a : Interval) (q : ℚ) : Interval :=
  if q < 0 then ⟨qfloor (a.hi*q),qceil (a.lo*q)⟩
  else ⟨qfloor (a.lo*q),qceil (a.hi*q)⟩

def atanhLog (x : ℚ) : Interval :=
  let z := (x-1)/(x+1)
  let s := (List.range 18).foldl (fun (t : Interval) (j : Nat) =>
    let term := 2*fix*z^(2*j+1)/(2*(j : ℚ)+1)
    plus t ⟨qfloor term,qceil term⟩) ⟨0,0⟩
  let residual := qceil (2*fix*z^37/(37*(1-z*z)))
  ⟨s.lo,s.hi+residual⟩

def lnTwo : Interval := atanhLog 2

def pow2q (e : ℤ) : ℚ :=
  if e < 0 then 1 / (2 : ℚ)^e.natAbs else (2 : ℚ)^e.toNat

def logRat (q : ℚ) : Interval :=
  let e0 : ℤ := (Nat.log2 q.num.natAbs : ℤ) - Nat.log2 q.den
  let e := if q < pow2q e0 then e0-1 else e0
  plus (scale lnTwo (e : ℚ)) (atanhLog (q/pow2q e))

def atanSmallPos (x : ℚ) : Interval :=
  let s := (List.range 18).foldl (fun (t : Interval) (j : Nat) =>
    let term := (if j%2=0 then (fix : ℚ) else -fix)*x^(2*j+1)/(2*(j : ℚ)+1)
    plus t ⟨qfloor term,qceil term⟩) ⟨0,0⟩
  ⟨s.lo, s.hi+qceil ((fix : ℚ)*x^37/37)⟩

def atanSmall (x : ℚ) : Interval :=
  if x<0 then scale (atanSmallPos (-x)) (-1) else atanSmallPos x

def piBounds : Interval := plus (scale (atanSmall (1/5)) 16) (scale (atanSmall (1/239)) (-4))

def atanUnit (x : ℚ) : Interval :=
  if 1/2 < x then plus (scale piBounds (1/4)) (atanSmall ((x-1)/(x+1)))
  else atanSmall x

def atanBounds (x : ℚ) : Interval :=
  let u := if x<0 then -x else x
  let b := if 1<u then plus (scale piBounds (1/2)) (scale (atanUnit (1/u)) (-1))
    else atanUnit u
  if x<0 then scale b (-1) else b

def logNode (i : Nat) : Interval := atanhLog ((128+(i : ℚ))/128)
def logShift (i : Nat) : Interval := plus (scale lnTwo i) (scale (logRat coord) (-2))

structure Lookup where
  nodes : Array Interval
  shifts : Array Interval

instance : Inhabited Interval := ⟨⟨0,0⟩⟩

def squaredLog (table : Lookup) (d : ℤ) (upper : Bool) : ℤ :=
  let e := Nat.log2 d.toNat
  let pow : ℤ := 2^e
  let k := d*128/pow
  let left := d*128-k*pow
  let den := (k+(if upper then 0 else 1))*pow
  let a := table.nodes[(k-128).toNat]!
  let b := table.shifts[e]!
  if upper then a.hi+b.hi+(-(-fix*left/den)) else a.lo+b.lo+fix*left/den

def checkLookup (t : Lookup) : Bool :=
  t.nodes.size == 129 && t.shifts.size == 80 &&
  (List.range 129).all (fun i =>
    let a := t.nodes[i]!
    let b := logNode i
    a.lo == b.lo && a.hi == b.hi) &&
  (List.range 80).all (fun i =>
    let a := t.shifts[i]!
    let b := logShift i
    a.lo == b.lo && a.hi == b.hi)

end OddZetaSix.B40a.Cert
