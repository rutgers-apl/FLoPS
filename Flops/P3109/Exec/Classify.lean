import Flops.P3109.Exec.Decode

namespace p3109_format
namespace Exec

/--
Executable classification of `Bits f` in terms of decode classes.
-/
def classify (x : Bits f) : Decoded f :=
  decode x

def classSign (x : Bits f) : Option Bool :=
  match decode x with
  | .nan => none
  | .posInf => some false
  | .negInf => some true
  | .finite fields => some fields.sign

@[inline]
def finiteClass (x : Bits f) : Option FiniteClass :=
  match decode x with
  | .finite fields => some fields.cls
  | _ => none

end Exec
end p3109_format
