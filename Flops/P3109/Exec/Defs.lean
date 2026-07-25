import Flops.P3109.Defs

namespace p3109_format
namespace Exec

/--
`Bits f` is the canonical executable representation for a P3109 datum:
the `K`-bit code point specified by the standard.
-/
abbrev Bits (f : p3109_format) := Fin (2 ^ f.K)

def bitwidth (f : p3109_format) : Nat := f.K

def precision (f : p3109_format) : Nat := f.P

def signedness (f : p3109_format) : Signedness := f.s

def domain (f : p3109_format) : Domain := f.d

def exponentBits (f : p3109_format) : Nat := f.W

def trailingBits (f : p3109_format) : Nat := f.P - 1

def exponentBias (f : p3109_format) : Int := f.bias

def code (x : Bits f) : Nat := x.val

def maxCode (f : p3109_format) : Nat := 2 ^ f.K - 1

def signBase (f : p3109_format) : Nat := 2 ^ (f.K - 1)

def exponentModulus (f : p3109_format) : Nat := 2 ^ trailingBits f

def nanCode (f : p3109_format) : Nat :=
  match f.s with
  | .signed => signBase f
  | .unsigned => maxCode f

def posInfCode? (f : p3109_format) : Option Nat :=
  match f.s, f.d with
  | .signed, .extended => some (signBase f - 1)
  | .unsigned, .extended => some (maxCode f - 1)
  | _, _ => none

def negInfCode? (f : p3109_format) : Option Nat :=
  match f.s, f.d with
  | .signed, .extended => some (maxCode f)
  | _, _ => none

def negativeRegion (f : p3109_format) (x : Bits f) : Bool :=
  match f.s with
  | .signed => signBase f < x.val
  | .unsigned => false

def magnitudeCode (f : p3109_format) (x : Bits f) : Nat :=
  if negativeRegion f x then
    x.val - signBase f
  else
    x.val

def trailingField (f : p3109_format) (x : Bits f) : Nat :=
  magnitudeCode f x % exponentModulus f

def exponentField (f : p3109_format) (x : Bits f) : Nat :=
  magnitudeCode f x / exponentModulus f

end Exec
end p3109_format
