import Flops.P3109.Exec.Ops.Runtime
import Flops.P3109.Exec.Project
import Mathlib.Data.EReal.Operations
import Mathlib.Data.EReal.Inv

namespace p3109_format
namespace Exec

/-- Exact absolute-value path kept as a convenience helper for the executable API. -/
def absProject
    (x : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  abs (f := f) x rnd sat

end Exec
end p3109_format
