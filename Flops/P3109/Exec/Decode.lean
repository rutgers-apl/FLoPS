import Flops.P3109.Exec.Defs

namespace p3109_format
namespace Exec

inductive FiniteClass where
  | zero
  | subnormal
  | normal
  deriving Repr, BEq, DecidableEq

structure FiniteFields (f : p3109_format) where
  sign : Bool
  exponentField : Nat
  trailingField : Nat
  cls : FiniteClass
  deriving Repr, BEq, DecidableEq

inductive Decoded (f : p3109_format) where
  | nan
  | posInf
  | negInf
  | finite (fields : FiniteFields f)
  deriving Repr, BEq, DecidableEq

def finiteClassOfMagnitude (f : p3109_format) (mag : Nat) : FiniteClass :=
  if mag = 0 then
    .zero
  else if mag / exponentModulus f = 0 then
    .subnormal
  else
    .normal

def finiteFieldsOfMagnitude (f : p3109_format) (sign : Bool) (mag : Nat) : FiniteFields f :=
  { sign := sign
    exponentField := mag / exponentModulus f
    trailingField := mag % exponentModulus f
    cls := finiteClassOfMagnitude f mag }

def decode (x : Bits f) : Decoded f :=
  let n := x.val
  if n = nanCode f then
    .nan
  else if posInfCode? f = some n then
    .posInf
  else if negInfCode? f = some n then
    .negInf
  else if negativeRegion f x then
    .finite (finiteFieldsOfMagnitude f true (n - signBase f))
  else
    .finite (finiteFieldsOfMagnitude f false n)

def isNaN (x : Bits f) : Bool :=
  match decode x with
  | .nan => true
  | _ => false

def isInfinite (x : Bits f) : Bool :=
  match decode x with
  | .posInf
  | .negInf => true
  | _ => false

def isFinite (x : Bits f) : Bool :=
  match decode x with
  | .finite _ => true
  | _ => false

def signMinus (x : Bits f) : Bool :=
  match decode x with
  | .negInf => true
  | .finite fields => fields.sign
  | _ => false

def isZero (x : Bits f) : Bool :=
  match decode x with
  | .finite fields => fields.cls == .zero
  | _ => false

def isSubnormal (x : Bits f) : Bool :=
  match decode x with
  | .finite fields => fields.cls == .subnormal
  | _ => false

def isNormal (x : Bits f) : Bool :=
  match decode x with
  | .finite fields => fields.cls == .normal
  | _ => false

end Exec
end p3109_format
