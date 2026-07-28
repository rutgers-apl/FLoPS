import Flops.P3109.Exec.Encode
import Flops.P3109.Exec.Value
import Flops.P3109.Exec.Project.Runtime
import Flops.P3109.Exec.Classify
import Flops.P3109.Exec.Decode

namespace p3109_format
namespace Exec

/-- Negate exactly, then project according to the result format's specification. -/
def negate
    (x : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  project (f := f) (neg (fromBits x)) rnd sat

/-- Add with project pipeline. -/
def add
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  project (f := f) (addExact (f := f) a b) rnd sat

/-- Subtract with project pipeline. -/
def subtract
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  project (f := f) (subExact (f := f) a b) rnd sat

/-- Multiply with project pipeline. -/
def multiply
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  project (f := f) (mulExact (f := f) a b) rnd sat

/-- Divide with project pipeline. -/
def divRoundedValue (x y : Value f) (rnd : RoundingMode) : Value f :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInf, .posInf | .posInf, .negInf
  | .negInf, .posInf | .negInf, .negInf => .nan
  | _, .finite 0 _ => .nan
  | .posInf, .finite m _ =>
    if m < 0 then .negInf else .posInf
  | .negInf, .finite m _ =>
    if m < 0 then .posInf else .negInf
  | .finite _ _, .posInf => .finite 0 f.emin_lsb
  | .finite _ _, .negInf => .finite 0 f.emin_lsb
  | .finite 0 _, _ => .finite 0 f.emin_lsb
  | .finite m₁ e₁, .finite m₂ e₂ =>
    let neg := decide ((m₁ < 0) ≠ (m₂ < 0))
    roundFiniteRat f (Int.natAbs m₁) (Int.natAbs m₂) (e₁ - e₂) neg rnd

/-- Divide with the executable projection pipeline. -/
def divide
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  project (f := f) (divRoundedValue (f := f) a b rnd) rnd sat

/-- Fused multiply-add: `(x*y + z)` with one final project. -/
def fma
    (x y z : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  let c := fromBits (f := f) z
  project (f := f) (addExact (f := f) (mulExact (f := f) a b) c) rnd sat

/-- Fused add-add: `(x+y+z)` with one final project. -/
def faa
    (x y z : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let a := fromBits (f := f) x
  let b := fromBits (f := f) y
  let c := fromBits (f := f) z
  project (f := f) (addExact (f := f) (addExact (f := f) a b) c) rnd sat

/-- Absolute value through exact finite/infinity handling and exact finite encode. -/
def abs
    (x : Bits f)
    (_ : RoundingMode)
    (_ : SaturationMode) : Bits f :=
  let d := decode x
  match d with
  | .nan => encode d
  | .posInf => encode .posInf
  | .negInf => encode .posInf
  | .finite fields => encode (.finite { fields with sign := false })

/-- Computable bit-level comparison via the executable value ordering. -/
def isLess (x y : Bits f) : Bool :=
  match fromBits x, fromBits y with
  | .nan, _ | _, .nan => false
  | a, b => valueLT (f := f) a b

def isGreater (x y : Bits f) : Bool :=
  isLess (f := f) y x

def isEqual (x y : Bits f) : Bool :=
  match fromBits x, fromBits y with
  | .nan, _ | _, .nan => false
  | _, _ => x == y

def minimum (x y : Bits f) : Bits f :=
  match fromBits x, fromBits y with
  | .nan, _ | _, .nan => encodeValue (f := f) .nan
  | _, _ => if isLess x y then x else y

def maximum (x y : Bits f) : Bits f :=
  match fromBits x, fromBits y with
  | .nan, _ | _, .nan => encodeValue (f := f) .nan
  | _, _ => if isGreater x y then x else y

def absoluteValue (x : Bits f) : Bits f :=
  let d := decode x
  match d with
  | .nan => encode .nan
  | .posInf => encode .posInf
  | .negInf => encode .posInf
  | .finite fields => encode (.finite { fields with sign := false })

end Exec
end p3109_format
