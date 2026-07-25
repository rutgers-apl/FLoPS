import Flops.P3109.Exec.Encode
import Flops.P3109.Exec.Value
import Flops.P3109.Exec.Project.Runtime
import Flops.P3109.Exec.Classify
import Flops.P3109.Exec.Decode

namespace p3109_format
namespace Exec

/--
Signed negate at the bit level. This keeps the fast-path behavior used by the
existing executable codec layer.
-/
def negate (x : Bits f) : Bits f :=
  let d' : Decoded f :=
    let d := decode x
    match d with
    | .nan => .nan
    | .posInf =>
      match f.s with
      | .signed => .negInf
      | .unsigned => .posInf
    | .negInf => .posInf
    | .finite fields =>
      if _ : f.s = .signed then
        .finite { fields with sign := fields.sign.not }
      else
        .finite fields
  encode d'

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
  | .nan, _ => .finite 0 f.emin_lsb
  | _, .nan => .finite 0 f.emin_lsb
  | _, .posInf => .finite 0 f.emin_lsb
  | _, .negInf => .finite 0 f.emin_lsb
  | _, .finite 0 _ => .finite 0 f.emin_lsb
  | .posInf, .finite m _ =>
    if m < 0 then .negInf else .posInf
  | .negInf, .finite m _ =>
    if m < 0 then .posInf else .negInf
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
  valueLT (f := f) (fromBits x) (fromBits y)

def isGreater (x y : Bits f) : Bool :=
  valueLT (f := f) (fromBits y) (fromBits x)

def isEqual (x y : Bits f) : Bool :=
  x == y

def minimum (x y : Bits f) : Bits f :=
  if isLess x y then x else y

def maximum (x y : Bits f) : Bits f :=
  if isGreater x y then x else y

def absoluteValue (x : Bits f) : Bits f :=
  let d := decode x
  match d with
  | .nan => encode .nan
  | .posInf => encode .posInf
  | .negInf => encode .posInf
  | .finite fields => encode (.finite { fields with sign := false })

end Exec
end p3109_format

