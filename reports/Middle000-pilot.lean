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


/-- A fixed folding cut, or -1 for the unfolded cost. No histogram array updates. -/
def witnessCost (mid : ℚ) (cut : ℤ) : ℚ :=
  let p := 4*mid.num
  let d : ℤ := 4*(mid.den : ℤ)
  let K := (80*d/p).toNat
  let q := cut.toNat
  let walls := increasingZ (0 :: (p/2) :: ([16,17,25,34,59] : List ℤ).map
    (fun e => let r := e*d%p; min r (p-r)))
  let bags := (adjacent walls).map fun (l,r) =>
    let b := (l+r)/2
    let xs := (iRange b (25*d) p ++ iRange (p-b) (25*d) p).flatMap (middleSite p d)
    let scores := (xs.filter (fun z => 0 < z && z ≤ 16)).mergeSort (fun a b => decide (b ≤ a))
    let adjusted := scores.zipIdx.map fun (w,j) =>
      if cut < 0 then w else w-2*((j-q : Nat) : ℤ)
    (r-l,adjusted)
  let cost := ((nrange 1 17).map fun k =>
    min (40*d) ((bags.map fun (qty,ws) =>
      qty * ((ws.takeWhile (fun w => decide ((k:ℤ) ≤ w))).length : ℤ)).sum)).sum
  let line := K-q
  let charge := if cut < 0 then 0 else 80*d*(line:ℤ)-p*(((K+q+1)*line/2:Nat):ℤ)
  ((charge+cost:ℤ):ℚ)/(2000*d:ℤ)

def witnessOK (e : ArithRow × ℤ) : Bool :=
  let r := e.1
  let m := (r.left+r.right)/2
  decide (r.left < r.right ∧ 0 ≤ r.upper ∧
    (e.2 = -1 ∨ (0 ≤ e.2 ∧ e.2 ≤ (80*(m.den:ℤ)/m.num))) ∧
    qceil ((r.right-r.left)*witnessCost m e.2*bigUnit) ≤ r.upper)
set_option maxHeartbeats 0
set_option maxRecDepth 16384

def middle000 : List ArithRow := [
  ⟨qfrac 11 20, qfrac 93 169, 50104426⟩,
  ⟨qfrac 93 169, qfrac 38 69, 70057035⟩,
  ⟨qfrac 38 69, qfrac 43 78, 86327335⟩,
  ⟨qfrac 43 78, qfrac 59 107, 17844889⟩,
  ⟨qfrac 59 107, qfrac 75 136, 10125424⟩,
  ⟨qfrac 75 136, qfrac 16 29, 36697542⟩,
  ⟨qfrac 16 29, qfrac 21 38, 159107266⟩,
  ⟨qfrac 21 38, qfrac 68 123, 35566497⟩,
  ⟨qfrac 68 123, qfrac 31 56, 115150016⟩,
  ⟨qfrac 31 56, qfrac 118 213, 62541581⟩,
  ⟨qfrac 118 213, qfrac 41 74, 9205058⟩,
  ⟨qfrac 41 74, qfrac 51 92, 41768662⟩,
  ⟨qfrac 51 92, qfrac 76 137, 54213479⟩,
  ⟨qfrac 76 137, qfrac 5 9, 102877480⟩,
  ⟨qfrac 5 9, qfrac 84 151, 30426704⟩,
  ⟨qfrac 84 151, qfrac 59 106, 10794906⟩,
  ⟨qfrac 59 106, qfrac 93 167, 8204181⟩,
  ⟨qfrac 93 167, qfrac 34 61, 11796740⟩,
  ⟨qfrac 34 61, qfrac 43 77, 92537120⟩,
  ⟨qfrac 43 77, qfrac 19 34, 31280184⟩,
  ⟨qfrac 19 34, qfrac 118 211, 33044008⟩,
  ⟨qfrac 118 211, qfrac 33 59, 6199235⟩,
  ⟨qfrac 33 59, qfrac 80 143, 9066980⟩,
  ⟨qfrac 80 143, qfrac 75 134, 19629003⟩,
  ⟨qfrac 75 134, qfrac 14 25, 21882758⟩,
  ⟨qfrac 14 25, qfrac 93 166, 17199638⟩,
  ⟨qfrac 93 166, qfrac 51 91, 13374963⟩,
  ⟨qfrac 51 91, qfrac 32 57, 50339029⟩,
  ⟨qfrac 32 57, qfrac 41 73, 15540992⟩,
  ⟨qfrac 41 73, qfrac 50 89, 9457320⟩,
  ⟨qfrac 50 89, qfrac 59 105, 19187667⟩,
  ⟨qfrac 59 105, qfrac 68 121, 14030221⟩
]



def cuts : List ℤ := [141, 141, 141, 141, 141, 141, 140, 140, 140, 140, 140, 140, 140, 140, 142, 142, 142, 142, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 140, 140, 138, 137]
theorem firstShard : ((middle000.zip cuts).all witnessOK && decide (cuts.length = middle000.length)) = true := by decide +kernel
#print axioms firstShard
end OddZetaSix.B40a.Cert
