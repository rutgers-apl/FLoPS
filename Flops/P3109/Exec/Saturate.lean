import Flops.P3109.Exec.Value
import Flops.P3109.RoundingMode

namespace p3109_format
namespace Exec

def SatFinite : SaturationMode := SaturationMode.SatFinite
def SatPropagate : SaturationMode := SaturationMode.SatPropagate
def SatNone : SaturationMode := SaturationMode.SatNone

def intPow2 (n : Nat) : Int :=
  (2 : Int) ^ n

def maxFiniteValue (f : p3109_format) : Value f :=
  if _ : f.P = 1 then
    .finite 1 f.emax_lsb
  else
    let sub : Nat :=
      match f.P, f.s, f.d with
      | _, .signed, .finite => 1
      | _, .signed, .extended => 2
      | _, .unsigned, .finite => 2
      | 2, .unsigned, .extended => 1
      | _, .unsigned, .extended => 3
    .finite (Int.ofNat (2 ^ f.P) - Int.ofNat sub) f.emax_lsb

def minFiniteValue (f : p3109_format) : Value f :=
  if _ : f.s = .unsigned then
    .finite 0 f.emin_lsb
  else
    match maxFiniteValue f with
    | .finite m e => .finite (-m) e
    | _ => .finite 0 f.emin_lsb

def canonicalZero (f : p3109_format) : Value f :=
  .finite 0 f.emin_lsb

def finiteLE (m₁ : Int) (e₁ : Int) (m₂ : Int) (e₂ : Int) : Bool :=
  if _ : e₁ ≤ e₂ then
    decide (m₁ ≤ m₂ * intPow2 (Int.toNat (e₂ - e₁)))
  else
    decide (m₁ * intPow2 (Int.toNat (e₁ - e₂)) ≤ m₂)

def valueLE (x y : Value f) : Bool :=
  match x, y with
  | .nan, .nan => true
  | .nan, .negInf => false
  | .nan, .posInf => true
  | .nan, .finite m e => finiteLE 0 f.emin_lsb m e
  | .finite m e, .nan => finiteLE m e 0 f.emin_lsb
  | .posInf, .nan => false
  | .negInf, .nan => true
  | .negInf, _ => true
  | _, .posInf => true
  | .posInf, _ => false
  | _, .negInf => false
  | .finite m₁ e₁, .finite m₂ e₂ => finiteLE m₁ e₁ m₂ e₂

def valueLT (x y : Value f) : Bool :=
  valueLE x y && !(valueLE y x)

def inFiniteRange (f : p3109_format) (x : Value f) : Bool :=
  valueLE (minFiniteValue f) x && valueLE x (maxFiniteValue f)

def negOverflowValue (f : p3109_format) : Value f :=
  if _ : f.s = .signed then
    if _ : f.d = .extended then .negInf else minFiniteValue f
  else
    minFiniteValue f

def posOverflowValue (f : p3109_format) : Value f :=
  if _ : f.d = .extended then .posInf else maxFiniteValue f

/-- Saturate a rounded value according to the selected saturation mode and rounding mode. -/
def saturate (f : p3109_format) (x : Value f) (sat : SaturationMode) (rnd : RoundingMode) : Value f :=
  if inFiniteRange f x then
    x
  else
    match sat with
    | .SatFinite =>
      if valueLT x (minFiniteValue f) then minFiniteValue f else maxFiniteValue f
    | .SatPropagate =>
      match x with
      | .posInf => if _ : f.d = .extended then .posInf else maxFiniteValue f
      | .negInf => negOverflowValue f
      | _ => if valueLT x (minFiniteValue f) then minFiniteValue f else maxFiniteValue f
    | .SatNone =>
      match x with
      | .posInf =>
        if _ : f.d = .extended then .posInf else .nan
      | .negInf =>
        match f.s, f.d with
        | .signed, .extended => .negInf
        | _, _ => .nan
      | _ =>
        if valueLT x (minFiniteValue f) then
          match rnd with
          | .RZ | .RU => minFiniteValue f
          | _ =>
            match f.s, f.d with
            | .signed, .extended => .negInf
            | _, _ => .nan
        else
          match rnd, f.s, f.d with
          | .RZ, _, _ | .RD, _, _ => maxFiniteValue f
          | .RTO, .unsigned, .extended => maxFiniteValue f
          | _, _, .finite => .nan
          | _, _, .extended => .posInf

/-- Project-and-saturate helper for an internal executable value. -/
def saturateToMode (f : p3109_format) (x : Value f) (sat : SaturationMode) (rnd : RoundingMode) : Value f :=
  saturate f x sat rnd

end Exec
end p3109_format
