import Flops.P3109.Exec.Value
import Flops.P3109.RoundingMode
import Flops.Core.Exec.RoundKernel
import Mathlib.Data.Int.Log

namespace p3109_format
namespace Exec

variable {f : p3109_format}

def absNat (n : Int) : Nat :=
  Int.natAbs n

def vnumPow (f : p3109_format) : Nat :=
  2 ^ f.P

structure RoundFiniteCore (f : p3109_format) where
  am : Nat
  logAbs : Int
  E : Int
  shift : Int
  pow : Nat
  q : Nat
  r : Nat
  d : Nat
  qInt : Int
  qplus : Int
  sign : Int
  rounded : Int

structure RoundRatCore (f : p3109_format) where
  num : Nat
  den : Nat
  logAbs : Int
  E : Int
  shift : Int
  pow : Nat
  scaledNum : Nat
  scaledDen : Nat
  q : Nat
  r : Nat
  qInt : Int
  qplus : Int
  sign : Int
  rounded : Int

def floorLog2RatShift (num den : Nat) (e : Int) : Int :=
  Int.log 2 (((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ e)

def deterministicRoundAway (f : p3109_format)
    (mode : Flops.Exec.RoundKernel.Mode) (q r d : Nat) (E sign : Int) : Bool :=
  Flops.Exec.RoundKernel.roundAway f.P f.bias mode q r d E sign

def roundAwayInt (f : p3109_format) (q : Nat) (r d : Nat) (E : Int) (m : Int)
    (rnd : RoundingMode) : Bool :=
  match rnd with
  | .RD  => deterministicRoundAway f .RD q r d E m
  | .RU  => deterministicRoundAway f .RU q r d E m
  | .RZ  => deterministicRoundAway f .RZ q r d E m
  | .RNE => deterministicRoundAway f .RNE q r d E m
  | .RNA => deterministicRoundAway f .RNA q r d E m
  | .RTO => deterministicRoundAway f .RTO q r d E m
  | .StochasticA N R _ =>
    let p2 : Nat := 2 ^ N
    let q' : Nat := (r * p2) / d
    decide (q' + R ≥ p2)
  | .StochasticB N R _ =>
    let p2 : Nat := 2 ^ (N + 1)
    let q' : Nat := (r * p2) / d
    decide (q' + 2 * R + 1 ≥ p2)
  | .StochasticC N R _ =>
    let p2 : Nat := 2 ^ N
    let scaled : Nat := r * p2
    let q' : Nat := scaled / d
    let rem : Nat := scaled % d
    let rnite : Nat :=
      if 2 * rem < d ∨ (2 * rem = d ∧ Even q') then q' else q' + 1
    decide (rnite + R ≥ p2)

def roundFiniteCore (f : p3109_format) (m : Int) (e : Int) (rnd : RoundingMode) :
    RoundFiniteCore f :=
  let am : Nat := absNat m
  let logAbs : Int := Int.ofNat (Nat.log2 am) + e
  let E : Int := max logAbs (1 - f.bias) - f.P + 1
  let shift : Int := e - E
  let pow :=
    if _ : 0 ≤ shift then
      2 ^ Int.toNat shift
    else
      2 ^ Int.toNat (-shift)
  let q : Nat := if _ : 0 ≤ shift then absNat m * pow else am / pow
  let r : Nat := if _ : 0 ≤ shift then 0 else am % pow
  let d : Nat := if _ : 0 ≤ shift then 1 else pow
  let qInt : Int := q
  let qplus : Int := if roundAwayInt f q r d E m rnd then qInt + 1 else qInt
  let sign : Int := if m < 0 then -1 else 1
  let rounded : Int := sign * qplus
  { am := am
    logAbs := logAbs
    E := E
    shift := shift
    pow := pow
    q := q
    r := r
    d := d
    qInt := qInt
    qplus := qplus
    sign := sign
    rounded := rounded }

def roundRatCore (f : p3109_format) (num den : Nat) (e : Int) (neg : Bool)
    (rnd : RoundingMode) : RoundRatCore f :=
  let logAbs := floorLog2RatShift num den e
  let E : Int := max logAbs (1 - f.bias) - f.P + 1
  let shift : Int := e - E
  let pow :=
    if _ : 0 ≤ shift then
      2 ^ Int.toNat shift
    else
      2 ^ Int.toNat (-shift)
  let scaledNum := if _ : 0 ≤ shift then num * pow else num
  let scaledDen := if _ : 0 ≤ shift then den else den * pow
  let q : Nat := scaledNum / scaledDen
  let r : Nat := scaledNum % scaledDen
  let qInt : Int := q
  let sign : Int := if neg then -1 else 1
  let qplus : Int := if roundAwayInt f q r scaledDen E sign rnd then qInt + 1 else qInt
  let rounded : Int := sign * qplus
  { num := num
    den := den
    logAbs := logAbs
    E := E
    shift := shift
    pow := pow
    scaledNum := scaledNum
    scaledDen := scaledDen
    q := q
    r := r
    qInt := qInt
    qplus := qplus
    sign := sign
    rounded := rounded }

def roundFinite (f : p3109_format) (m : Int) (e : Int) (rnd : RoundingMode) :
    Value f :=
  if m = 0 then
    .finite 0 f.emin_lsb
  else
    let c := roundFiniteCore f m e rnd
    if Int.natAbs c.rounded = vnumPow f then
      .finite (c.rounded / 2) (c.E + 1)
    else
      .finite c.rounded c.E

def roundFiniteRat (f : p3109_format) (num den : Nat) (e : Int) (neg : Bool)
    (rnd : RoundingMode) : Value f :=
  if num = 0 ∨ den = 0 then
    .finite 0 f.emin_lsb
  else
    let c := roundRatCore f num den e neg rnd
    if Int.natAbs c.rounded = vnumPow f then
      .finite (c.rounded / 2) (c.E + 1)
    else
      .finite c.rounded c.E

/-- Round a kernel value through exact integer residue arithmetic for each mode.-/
def round (x : Value f) (rnd : RoundingMode) : Value f :=
  match x with
  | .nan => .nan
  | .posInf => .posInf
  | .negInf => .negInf
  | .finite m e => roundFinite f m e rnd
def roundToPrecision (x : Value f) (rnd : RoundingMode) : Value f :=
  round x rnd

end Exec
end p3109_format
