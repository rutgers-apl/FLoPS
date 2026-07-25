import Flops.P3109.Exec.Project.Runtime
import Flops.P3109.Rounding
import Flops.P3109.Bijection
import Flops.P3109.Projection

namespace p3109_format
namespace Exec

noncomputable def toBits (x : p3109 f) : Bits f :=
  let n : Fin (2 ^ f.K) := Classical.choose (p3109.bi_surj (f := f) x)
  -- `n` is guaranteed to map back to `x`.
  n

lemma toBits_fromBits (x : Bits f) : toBits (f := f) (p3109.n_to_p3109 (f := f) x) = x := by
  unfold toBits
  exact
    (p3109.bi_inj (f := f))
      (by
        simpa using
          (Classical.choose_spec (p3109.bi_surj (f := f) (p3109.n_to_p3109 (f := f) x))))

lemma fromBits_toBits (x : p3109 f) : toEReal (fromBits (f := f) (toBits (f := f) x)) = x.to_ereal := by
  let n : Fin (2 ^ f.K) := Classical.choose (p3109.bi_surj (f := f) x)
  have hsurj : p3109.n_to_p3109 n = x := by
    exact Classical.choose_spec (p3109.bi_surj (f := f) x)
  calc
    toEReal (fromBits (f := f) (toBits (f := f) x))
        = toEReal (fromBits (f := f) n) := by
          simp [toBits, n]
    _ = p3109.to_ereal (p3109.n_to_p3109 n) := by
      simpa using toEReal_fromBits (f := f) n
    _ = x.to_ereal := by simpa using congrArg p3109.to_ereal hsurj

/-- Reference wrapper for the old semantic pipeline: use `p3109.project` directly. -/
noncomputable def projectSpecBits
    (x : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  toBits (f := f) (@p3109.project f x rnd sat)
/-- Project raw extended-real values via the exec rounding and saturation pipeline. -/
noncomputable def projectEReal
    (x : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode) : Bits f :=
  let r : EReal := @round_to_precision f x rnd
  let s : EReal ⊕ Unit := @p3109_format.saturate f r sat rnd
  let hvs : s ∈ p3109_format.p3109.value_set f := by
    simpa [r, s] using (p3109_format.p3109.in_value_set (f := f) x rnd sat)
  let p : p3109 f := @p3109.encode f s hvs
  toBits (f := f) p

end Exec
end p3109_format
