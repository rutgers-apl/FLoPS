import Flops.P3109.Exec.Refinement

namespace p3109_format
namespace Exec

def evalTinySigned : p3109_format :=
  ⟨3, 2, Signedness.signed, Domain.extended, by decide, by decide⟩

def evalTinyP1Signed : p3109_format :=
  ⟨4, 1, Signedness.signed, Domain.extended, by decide, by decide⟩
def evalTinyUnsigned : p3109_format :=
  ⟨3, 2, Signedness.unsigned, Domain.extended, by decide, by decide⟩

def evalTinyUnsignedFin : p3109_format :=
  ⟨3, 2, Signedness.unsigned, Domain.finite, by decide, by decide⟩

example :
    round (f := evalTinySigned) (.finite 3 (-1)) RoundingMode.RNE =
      .finite 3 (-1) := by
  native_decide

example :
    roundAwayInt evalTinySigned 3 1 2 (-1) 7 RoundingMode.RNE = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5 RoundingMode.RNE = false := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5 RoundingMode.RNA = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5 RoundingMode.RTO = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 3 1 2 (-1) 7 RoundingMode.RTO = false := by
  native_decide

example :
    roundAwayInt evalTinyP1Signed 1 1 2 (-1) 3 RoundingMode.RNE = true := by
  native_decide

example :
    roundAwayInt evalTinyP1Signed 1 1 2 (-2) 3 RoundingMode.RNE = false := by
  native_decide

example :
    roundAwayInt evalTinyP1Signed 0 1 2 (-1) 1 RoundingMode.RTO = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticA 2 1 (by decide)) = false := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticA 2 2 (by decide)) = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticB 2 1 (by decide)) = false := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticB 2 2 (by decide)) = true := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticC 2 1 (by decide)) = false := by
  native_decide

example :
    roundAwayInt evalTinySigned 2 1 2 (-1) 5
      (RoundingMode.StochasticC 2 2 (by decide)) = true := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 5 (-2)) RoundingMode.RNE =
      .finite 2 (-1) := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 7 (-2)) RoundingMode.RNE =
      .finite 2 0 := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 5 (-2)) RoundingMode.RNA =
      .finite 3 (-1) := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 5 (-2)) RoundingMode.RTO =
      .finite 3 (-1) := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 5 (-2))
      (RoundingMode.StochasticA 2 1 (by decide)) =
      .finite 2 (-1) := by
  native_decide

example :
    round (f := evalTinySigned) (.finite 5 (-2))
      (RoundingMode.StochasticA 2 2 (by decide)) =
      .finite 3 (-1) := by
  native_decide

example :
    round (f := evalTinyP1Signed) (.finite 3 (-2)) RoundingMode.RNE =
      .finite 1 0 := by
  native_decide

example :
    round (f := evalTinyP1Signed) (.finite 3 (-3)) RoundingMode.RNE =
      .finite 1 (-2) := by
  native_decide

example :
    saturate evalTinySigned (.finite 99 0) SaturationMode.SatNone RoundingMode.RNE =
      (Value.posInf : Value evalTinySigned) := by
  native_decide

example :
    (project (f := evalTinySigned) (.finite 3 (-1))
      RoundingMode.RNE SaturationMode.SatNone).val = 3 := by
  native_decide

example :
    (reproject (f := evalTinySigned) ⟨1, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 1 := by
  native_decide

example :
    fromBits (project (f := evalTinyUnsigned) (.nan) RoundingMode.RNE SaturationMode.SatNone)
      = Value.nan := by
  native_decide

example :
    (project (f := evalTinyUnsigned) (.posInf) RoundingMode.RNE SaturationMode.SatNone).val =
      (posInfCode? evalTinyUnsigned).getD 0 := by
  native_decide

example :
    (project (f := evalTinyUnsigned) (.finite 5 0) RoundingMode.RNE SaturationMode.SatNone).val =
      (posInfCode? evalTinyUnsigned).getD 0 := by
  native_decide

example :
    saturate (f := evalTinyUnsignedFin) (.finite 99 0) SaturationMode.SatFinite RoundingMode.RNE =
      maxFiniteValue (evalTinyUnsignedFin) := by
  native_decide

example :
    saturate (f := evalTinyUnsignedFin) (.finite (-3) 0) SaturationMode.SatNone RoundingMode.RNE =
      (Value.nan : Value evalTinyUnsignedFin) := by
  native_decide

example :
    (add (f := evalTinySigned) ⟨1, by decide⟩ ⟨1, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 2 := by
  native_decide

example :
    (subtract (f := evalTinySigned) ⟨2, by decide⟩ ⟨1, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 1 := by
  native_decide

example :
    (multiply (f := evalTinySigned) ⟨1, by decide⟩ ⟨2, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 1 := by
  native_decide

example :
    (fma (f := evalTinySigned) ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 2 := by
  native_decide

example :
    (faa (f := evalTinySigned) ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = 3 := by
  native_decide

-- Special values are handled by the executable pipeline deterministically.
example :
    round (f := evalTinySigned) .nan RoundingMode.RNE =
      .nan := by
  native_decide

example :
    round (f := evalTinySigned) .posInf RoundingMode.RNE =
      .posInf := by
  native_decide

example :
    round (f := evalTinySigned) .negInf RoundingMode.RNE =
      .negInf := by
  native_decide

-- Saturation edge behavior for overflow and signedness-sensitive domains.
example :
    saturate evalTinySigned (.finite 99 0) SaturationMode.SatFinite RoundingMode.RNE =
      maxFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.finite (-99) 0) SaturationMode.SatFinite RoundingMode.RNE =
      minFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.posInf) SaturationMode.SatFinite RoundingMode.RNE =
      maxFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.negInf) SaturationMode.SatFinite RoundingMode.RNE =
      minFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.finite 99 0) SaturationMode.SatPropagate RoundingMode.RNE =
      maxFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.finite (-99) 0) SaturationMode.SatNone RoundingMode.RZ =
      minFiniteValue evalTinySigned := by
  native_decide

example :
    saturate evalTinySigned (.finite 99 0) SaturationMode.SatNone RoundingMode.RU =
      .posInf := by
  native_decide

-- Executable encoding for special and small finite values.
example :
    (encodeValue (f := evalTinySigned) .nan).val = nanCode evalTinySigned := by
  native_decide

example :
    (encodeValue (f := evalTinySigned) .posInf).val = (posInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (encodeValue (f := evalTinySigned) .negInf).val = (negInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (encodeValue (f := evalTinySigned) (.finite 0 evalTinySigned.emin_lsb)).val = 0 := by
  native_decide

example :
    (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb)).val = 1 := by
  native_decide

example :
    (encodeValue (f := evalTinySigned) (.finite (-1) evalTinySigned.emin_lsb)).val =
      signBase evalTinySigned + 1 := by
  native_decide

-- Project/reproject special and overflow behavior stays in executable bits.
example :
    fromBits (project (f := evalTinySigned) .nan RoundingMode.RNE SaturationMode.SatNone)
      = Value.nan := by
  native_decide

example :
    (project (f := evalTinySigned) .posInf RoundingMode.RNE SaturationMode.SatNone).val =
      (posInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (project (f := evalTinySigned) .negInf RoundingMode.RNE SaturationMode.SatNone).val =
      (negInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (project (f := evalTinySigned) (.finite 99 0) RoundingMode.RNE SaturationMode.SatNone).val =
      (posInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (project (f := evalTinySigned) (.finite (-99) 0) RoundingMode.RNE SaturationMode.SatNone).val =
      (negInfCode? evalTinySigned).getD 0 := by
  native_decide

example :
    (project (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb)
      RoundingMode.RNE SaturationMode.SatNone).val = 1 := by
  native_decide

example :
    (reproject (f := evalTinySigned) (Fin.mk 1 (by decide))
      RoundingMode.RNE SaturationMode.SatNone).val = 1 := by
  native_decide

example :
    (add (f := evalTinySigned) ⟨2, by decide⟩ ⟨2, by decide⟩
      RoundingMode.RNE SaturationMode.SatNone).val = (posInfCode? evalTinySigned).getD 0 := by
  native_decide


/-!
# Regression tests for P3109 saturation and projection (§4.7.3 / §4.7.5)

These examples pin down the NaN-faithful pipeline and the July 2026 saturation
table:

* `SatNone` on a finite-domain format clamps positive overflow only for RD/RZ
  and negative overflow only for RU/RZ. Every other overflow result is NaN,
  including positive and negative infinity.
* Extended-domain infinity propagation remains intact. The unsigned,
  extended RTO rule still clamps a finite positive overflow to `M hi`.

* P3109 §4.7.3/§4.7.5 say `ωProject(NaN) → NaN`
  and `ωSaturate(*, *, NaN, *, *) → NaN`.  The executable `round` and ordinary
  `project` pipeline now propagate `NaN`.
-/

/-- Unsigned, extended tiny format. -/
def rtUnsignedExtended : p3109_format :=
  ⟨5, 2, Signedness.unsigned, Domain.extended, by decide, by decide⟩

/-- Unsigned, finite tiny format. -/
def rtUnsignedFinite : p3109_format :=
  ⟨5, 2, Signedness.unsigned, Domain.finite, by decide, by decide⟩

def rtSignedFinite : p3109_format :=
  ⟨5, 2, Signedness.signed, Domain.finite, by decide, by decide⟩

/-! ## Finite-domain `SatNone` -/

-- Positive directed overflow clamps only for RD and RZ.
example :
    saturate rtSignedFinite (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RD
      = maxFiniteValue rtSignedFinite := by native_decide

example :
    saturate rtSignedFinite (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RZ
      = maxFiniteValue rtSignedFinite := by native_decide

example :
    saturate rtSignedFinite (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RNE
      = Value.nan := by native_decide

example :
    saturate rtSignedFinite (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RU
      = Value.nan := by native_decide

example :
    saturate rtSignedFinite (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RTO
      = Value.nan := by native_decide

-- Negative directed overflow clamps only for RU and RZ.
example :
    saturate rtSignedFinite (Value.finite (-1000000) 0)
        SaturationMode.SatNone RoundingMode.RU
      = minFiniteValue rtSignedFinite := by native_decide

example :
    saturate rtSignedFinite (Value.finite (-1000000) 0)
        SaturationMode.SatNone RoundingMode.RZ
      = minFiniteValue rtSignedFinite := by native_decide

example :
    saturate rtSignedFinite (Value.finite (-1000000) 0)
        SaturationMode.SatNone RoundingMode.RD
      = Value.nan := by native_decide

example :
    saturate rtSignedFinite (Value.finite (-1000000) 0)
        SaturationMode.SatNone RoundingMode.RNE
      = Value.nan := by native_decide

-- Finite-domain infinities are NaN, independent of signedness.
example :
    saturate rtUnsignedFinite Value.posInf SaturationMode.SatNone RoundingMode.RTO
      = Value.nan := by native_decide

example :
    saturate rtSignedFinite Value.negInf SaturationMode.SatNone RoundingMode.RZ
      = Value.nan := by native_decide

/-! ## Extended-domain `SatNone` -/

-- Extended-domain positive infinity remains infinity.
example :
    saturate rtUnsignedExtended Value.posInf SaturationMode.SatNone RoundingMode.RTO
      = Value.posInf := by native_decide

-- The unsigned extended RTO exception clamps finite positive overflow.
example :
    saturate rtUnsignedExtended (Value.finite 1000000 0)
        SaturationMode.SatNone RoundingMode.RTO
      = maxFiniteValue rtUnsignedExtended := by native_decide

/-! ## Semantic `saturate` on `⊤` -/

variable {f : p3109_format}

/-- Semantic regression: for an extended-domain format, saturating `+∞`
(`⊤`) under `SatNone`/`ToOdd` yields `+∞` (`Sum.inl ⊤`), matching
`ωSaturate(SatNone, *, +∞, *, Extended) → +∞`. -/
example (hd : f.d = Domain.extended) :
    @p3109_format.saturate f ⊤ SaturationMode.SatNone RoundingMode.RTO = Sum.inl ⊤ := by
  unfold p3109_format.saturate
  rw [if_neg]
  · simp [hd]
  · rintro ⟨h1, _⟩
    rw [p3109.finite_to_ereal_eq _ p3109.max_is_finite] at h1
    exact (not_le_of_gt (EReal.coe_lt_top _)) h1

/-! ## NaN propagation (`native_decide`) -/

-- Executable `saturate` preserves `NaN`.
example :
    saturate rtUnsignedExtended Value.nan SaturationMode.SatNone RoundingMode.RNE
      = Value.nan := by native_decide

-- Executable `round` preserves `NaN`.
example :
    round (f := rtUnsignedExtended) Value.nan RoundingMode.RNE
      = Value.nan := by native_decide

-- The ordinary bit projection decodes back to `NaN`.
example :
    fromBits (project (f := rtUnsignedExtended) Value.nan RoundingMode.RNE
        SaturationMode.SatNone)
      = Value.nan := by native_decide

example :
    saturate rtUnsignedExtended (round (f := rtUnsignedExtended) Value.nan RoundingMode.RNE)
        SaturationMode.SatNone RoundingMode.RNE
      = Value.nan := by native_decide

/-! ## Issue 2 — NaN-faithful spec lemmas -/

-- `ωSaturate(*, *, NaN, *, *) → NaN` at the closed-extended-real level.
example (sat : SaturationMode) (rnd : RoundingMode) :
    saturateC (f := f) (Sum.inr ()) sat rnd = Sum.inr () := rfl

-- `ωProject(NaN) → NaN` at the closed-extended-real level.
example (rnd : RoundingMode) (sat : SaturationMode) :
    projectCereal (f := f) (Sum.inr ()) rnd sat = Sum.inr () := rfl

-- NaN-faithful saturation refinement, stated against `toCereal`.
example (x : Value f) (sat : SaturationMode) (rnd : RoundingMode) :
    toCereal (saturate f x sat rnd) = saturateC (f := f) (toCereal x) sat rnd :=
  saturate_toCereal_refines x sat rnd

-- NaN-faithful projection refinement, stated against `toCereal`.
example (x : Value f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (saturate f (round x rnd) sat rnd) =
      projectCereal (f := f) (toCereal x) rnd sat :=
  saturate_round_toCereal_refines x rnd sat

end Exec
end p3109_format
