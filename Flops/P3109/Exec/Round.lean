import Flops.P3109.Exec.Round.Runtime
import Flops.P3109.Rounding

namespace p3109_format
namespace Exec

variable {f : p3109_format}

/-- Semantic reference wrapper retained by the compatibility module. -/
noncomputable def roundToPrecisionFromEReal (x : EReal) (rnd : RoundingMode) : EReal :=
  @round_to_precision f x rnd

end Exec
end p3109_format
