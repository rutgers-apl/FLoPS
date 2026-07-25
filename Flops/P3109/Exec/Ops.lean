import Flops.P3109.Exec.Ops.Runtime
import Flops.P3109.Exec.Project
import Mathlib.Data.EReal.Operations
import Mathlib.Data.EReal.Inv

namespace p3109_format
namespace Exec

/-- Exact absolute-value path kept as a convenience helper for the executable API. -/
noncomputable def absProject
    (x : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let r := toEReal (fromBits x)
  match r with
  | ⊤ => projectEReal (⊤ : EReal) rnd sat
  | ⊥ => projectEReal (⊥ : EReal) rnd sat
  | (x : ℝ) => projectEReal ((|x| : ℝ) : EReal) rnd sat

end Exec
end p3109_format
