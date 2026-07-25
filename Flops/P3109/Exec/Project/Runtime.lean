import Flops.P3109.Exec.Encode
import Flops.P3109.Exec.Value
import Flops.P3109.Exec.Round.Runtime
import Flops.P3109.Exec.Saturate

namespace p3109_format
namespace Exec

def finiteValueCode (f : p3109_format) (m e : Int) : Nat :=
  let mag := Int.natAbs m
  if mag = 0 then
    0
  else
    let half := 2 ^ (f.P - 1)
    let magnitude :=
      if e = f.emin_lsb ∧ mag < half then
        mag
      else
        (mag - half) + Int.toNat (e + Int.ofNat f.P - 1 + f.bias) * half
    if f.s = .signed ∧ m < 0 then
      signBase f + magnitude
    else
      magnitude

def encodeValueNat (f : p3109_format) (x : Value f) : Nat :=
  match x with
  | .nan => encodeNat (f := f) .nan
  | .posInf => encodeNat (f := f) .posInf
  | .negInf => encodeNat (f := f) .negInf
  | .finite m e => finiteValueCode f m e

def encodeValue (x : Value f) : Bits f :=
  ⟨encodeValueNat f x % 2 ^ f.K, Nat.mod_lt _ (pow_pos (Nat.succ_pos 1) f.K)⟩

/-- Project a kernel value into executable bit-level format via the exec pipeline. -/
def project
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  encodeValue (f := f) (saturate f (round (f := f) x rnd) sat rnd)
/-- Lift a raw bit pattern through decode+project unchanged (no-op on semantics). -/
def reproject
    (x : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  project (f := f) (fromBits x) rnd sat

end Exec
end p3109_format

