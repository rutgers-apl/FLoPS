import Flops.P3109.Exec.Defs
import Flops.P3109.Exec.Decode
import Flops.P3109.Exec.Encode
import Flops.P3109.Exec.Project
import Flops.P3109.Exec.Refinement

namespace p3109_format
namespace Exec

def tinySignedExtended : p3109_format :=
  ⟨4, 3, Signedness.signed, Domain.extended, by decide, by decide⟩

def tinySignedFinite : p3109_format :=
  ⟨4, 3, Signedness.signed, Domain.finite, by decide, by decide⟩

def tinySignedNarrow : p3109_format :=
  ⟨3, 2, Signedness.signed, Domain.extended, by decide, by decide⟩

def tinyUnsignedExtended : p3109_format :=
  ⟨5, 2, Signedness.unsigned, Domain.extended, by decide, by decide⟩

def tinyUnsignedFinite : p3109_format :=
  ⟨5, 2, Signedness.unsigned, Domain.finite, by decide, by decide⟩

def tinyUnsignedNarrow : p3109_format :=
  ⟨3, 2, Signedness.unsigned, Domain.extended, by decide, by decide⟩

def tinyUnsignedNarrowFinite : p3109_format :=
  ⟨3, 2, Signedness.unsigned, Domain.finite, by decide, by decide⟩

def tinySignedP1Extended : p3109_format :=
  ⟨4, 1, Signedness.signed, Domain.extended, by decide, by decide⟩

def tinyUnsignedP1Extended : p3109_format :=
  ⟨3, 1, Signedness.unsigned, Domain.extended, by decide, by decide⟩

def tinyUnsignedPEqualsK : p3109_format :=
  ⟨5, 5, Signedness.unsigned, Domain.extended, by decide, by decide⟩

-- Special-code decode checks for representative tiny formats.
example : decode (f := tinySignedNarrow) ⟨0, by decide⟩ = .finite
  { sign := false, exponentField := 0, trailingField := 0, cls := .zero } := by
  native_decide

example : decode (f := tinySignedNarrow) ⟨nanCode tinySignedNarrow, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinySignedNarrow) ⟨3, by decide⟩ = .posInf := by
  native_decide

example : decode (f := tinySignedNarrow) ⟨7, by decide⟩ = .negInf := by
  native_decide

example : decode (f := tinyUnsignedNarrow) ⟨0, by decide⟩ = .finite
  { sign := false, exponentField := 0, trailingField := 0, cls := .zero } := by
  native_decide

example : decode (f := tinyUnsignedNarrow) ⟨nanCode tinyUnsignedNarrow, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinyUnsignedNarrow) ⟨6, by decide⟩ = .posInf := by
  native_decide

example : classify (f := tinyUnsignedNarrow) ⟨6, by decide⟩ = .posInf := by
  native_decide

example : isNaN (f := tinyUnsignedNarrow) ⟨nanCode tinyUnsignedNarrow, by decide⟩ = true := by
  native_decide

example : isInfinite (f := tinyUnsignedNarrow) ⟨6, by decide⟩ = true := by
  native_decide

example : isFinite (f := tinyUnsignedNarrow) ⟨6, by decide⟩ = false := by
  native_decide

example : signMinus (f := tinyUnsignedNarrow) ⟨6, by decide⟩ = false := by
  native_decide

example : isZero (f := tinySignedNarrow) ⟨0, by decide⟩ = true := by
  native_decide

example : isSubnormal (f := tinyUnsignedNarrow) ⟨1, by decide⟩ = true := by
  native_decide

example : isNormal (f := tinySignedNarrow) ⟨2, by decide⟩ = true := by
  native_decide

example : decode (f := tinyUnsignedP1Extended) ⟨0, by decide⟩ = .finite
  { sign := false, exponentField := 0, trailingField := 0, cls := .zero } := by
  native_decide

example : decode (f := tinyUnsignedP1Extended) ⟨nanCode tinyUnsignedP1Extended, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinyUnsignedP1Extended) ⟨6, by decide⟩ = .posInf := by
  native_decide

example : decode (f := tinySignedFinite) ⟨0, by decide⟩ = .finite
  { sign := false, exponentField := 0, trailingField := 0, cls := .zero } := by
  native_decide

example : decode (f := tinyUnsignedFinite) ⟨0, by decide⟩ = .finite
  { sign := false, exponentField := 0, trailingField := 0, cls := .zero } := by
  native_decide

example : decode (f := tinySignedExtended) ⟨nanCode tinySignedExtended, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinySignedExtended) ⟨7, by decide⟩ = .posInf := by
  native_decide

example : decode (f := tinySignedExtended) ⟨15, by decide⟩ = .negInf := by
  native_decide

example : decode (f := tinyUnsignedExtended) ⟨nanCode tinyUnsignedExtended, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinyUnsignedExtended) ⟨30, by decide⟩ = .posInf := by
  native_decide

example : decode (f := tinySignedP1Extended) ⟨nanCode tinySignedP1Extended, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinySignedP1Extended) ⟨7, by decide⟩ = .posInf := by
  native_decide

example : decode (f := tinySignedP1Extended) ⟨15, by decide⟩ = .negInf := by
  native_decide

example : decode (f := tinyUnsignedPEqualsK) ⟨nanCode tinyUnsignedPEqualsK, by decide⟩ = .nan := by
  native_decide

example : decode (f := tinyUnsignedPEqualsK) ⟨30, by decide⟩ = .posInf := by
  native_decide

-- Exhaustive encode/decode round-trip for all finite-size code spaces.
example : ∀ x : Bits tinySignedNarrow, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinySignedNarrow.K = x
  rw [encode_decode_eq (f := tinySignedNarrow) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinyUnsignedNarrow, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinyUnsignedNarrow.K = x
  rw [encode_decode_eq (f := tinyUnsignedNarrow) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinySignedExtended, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinySignedExtended.K = x
  rw [encode_decode_eq (f := tinySignedExtended) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinyUnsignedExtended, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinyUnsignedExtended.K = x
  rw [encode_decode_eq (f := tinyUnsignedExtended) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinySignedP1Extended, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinySignedP1Extended.K = x
  rw [encode_decode_eq (f := tinySignedP1Extended) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinyUnsignedPEqualsK, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinyUnsignedPEqualsK.K = x
  rw [encode_decode_eq (f := tinyUnsignedPEqualsK) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinyUnsignedP1Extended, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinyUnsignedP1Extended.K = x
  rw [encode_decode_eq (f := tinyUnsignedP1Extended) x]
  exact Nat.mod_eq_of_lt x.isLt

example : ∀ x : Bits tinyUnsignedNarrowFinite, encode (decode x) = x := by
  intro x
  apply Fin.ext
  change encodeNat (decode x) % 2 ^ tinyUnsignedNarrowFinite.K = x
  rw [encode_decode_eq (f := tinyUnsignedNarrowFinite) x]
  exact Nat.mod_eq_of_lt x.isLt

-- The re-encode helper is definitional on every code point.
example : ∀ x : Bits tinyUnsignedNarrow, reencode x = x := by
  intro x
  exact reencode_eq x

example : ∀ x : Bits tinySignedFinite, reencode x = x := by
  intro x
  exact reencode_eq x

example : ∀ x : Bits tinyUnsignedFinite, reencode x = x := by
  intro x
  exact reencode_eq x

example : ∀ x : Bits tinyUnsignedNarrowFinite, reencode x = x := by
  intro x
  exact reencode_eq x


-- Project/reproject semantic checks through the executable projection pipeline.
example :
    ∀ x : Value tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (project (f := tinySignedNarrow) x rnd sat ))
      = toEReal
          (fromBits
            (projectSpecBits (f := tinySignedNarrow) (toEReal x) rnd sat
              )) := by
  intro x rnd sat
  rw [project_value_refines (f := tinySignedNarrow) x rnd sat ]
  unfold projectSpecBits
  rw [toBits_refines]

example :
    ∀ x : Value tinyUnsignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (project (f := tinyUnsignedNarrow) x rnd sat ))
      = toEReal
          (fromBits
            (projectSpecBits (f := tinyUnsignedNarrow) (toEReal x) rnd sat
              )) := by
  intro x rnd sat
  rw [project_value_refines (f := tinyUnsignedNarrow) x rnd sat ]
  unfold projectSpecBits
  rw [toBits_refines]

example :
    ∀ x : Value tinyUnsignedP1Extended,
    ∀ rnd sat,
    toEReal (fromBits (project (f := tinyUnsignedP1Extended) x rnd sat ))
      = toEReal
          (fromBits
            (projectSpecBits (f := tinyUnsignedP1Extended) (toEReal x) rnd sat
              )) := by
  intro x rnd sat
  rw [project_value_refines (f := tinyUnsignedP1Extended) x rnd sat ]
  unfold projectSpecBits
  rw [toBits_refines]

example :
    ∀ x : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (reproject (f := tinySignedNarrow) x rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          (toEReal (fromBits x)) rnd sat) := by
  intro x rnd sat
  unfold reproject
  simpa using
    (project_value_refines (f := tinySignedNarrow) (fromBits x) rnd sat
      )

-- The public refinement import exposes closed-extended-real specifications for
-- every arithmetic, comparison, and extrema operation.
example (x : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (negate x rnd sat)) =
      projectCereal (f := f) (cerealNeg (toCereal (fromBits x))) rnd sat :=
  negate_refines x rnd sat

example (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (add x y rnd sat)) =
      projectCereal (f := f)
        (cerealAdd (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  add_refines x y rnd sat

example (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (subtract x y rnd sat)) =
      projectCereal (f := f)
        (cerealSub (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  subtract_refines x y rnd sat

example (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (multiply x y rnd sat)) =
      projectCereal (f := f)
        (cerealMul (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  multiply_refines x y rnd sat

example (x y z : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (fma x y z rnd sat)) =
      projectCereal (f := f)
        (cerealAdd
          (cerealMul (toCereal (fromBits x)) (toCereal (fromBits y)))
          (toCereal (fromBits z))) rnd sat :=
  fma_refines x y z rnd sat

example (x y z : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (faa x y z rnd sat)) =
      projectCereal (f := f)
        (cerealAdd
          (cerealAdd (toCereal (fromBits x)) (toCereal (fromBits y)))
          (toCereal (fromBits z))) rnd sat :=
  faa_refines x y z rnd sat

example (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (divide x y rnd sat)) =
      projectCereal (f := f)
        (cerealDiv (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  div_refines x y rnd sat

example (x y : Bits f) :
    isLess x y = cerealLT (toCereal (fromBits x)) (toCereal (fromBits y)) :=
  isLess_refines x y

example (x y : Bits f) :
    isGreater x y = cerealLT (toCereal (fromBits y)) (toCereal (fromBits x)) :=
  isGreater_refines x y

example (x y : Bits f) :
    isEqual x y = cerealEq (toCereal (fromBits x)) (toCereal (fromBits y)) :=
  isEqual_refines x y

example (x y : Bits f) :
    toCereal (fromBits (minimum x y)) =
      cerealMin (toCereal (fromBits x)) (toCereal (fromBits y)) :=
  minimum_refines x y

example (x y : Bits f) :
    toCereal (fromBits (maximum x y)) =
      cerealMax (toCereal (fromBits x)) (toCereal (fromBits y)) :=
  maximum_refines x y



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
## D1 arithmetic edge cases

These executable checks mirror the exceptional-value rules in P3109/D1
Sections 4.10--4.12. FLoPS intentionally represents zero with the finite
`subnormal` case internally; decoding a projected zero therefore yields
`Value.finite 0 emin_lsb`.
-/

-- Addition and subtraction propagate NaN and reject indeterminate infinities.
example :
    fromBits (add (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .nan)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

example :
    fromBits (add (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .posInf)
        (encodeValue (f := evalTinySigned) .negInf)
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

example :
    fromBits (subtract (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .posInf)
        (encodeValue (f := evalTinySigned) .posInf)
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

-- Finite multiplication by zero is zero; zero times infinity is NaN.
example :
    fromBits (multiply (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 0 evalTinySigned.emin_lsb))
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        RoundingMode.RNE SaturationMode.SatNone) =
      Value.finite 0 evalTinySigned.emin_lsb := by
  native_decide

example :
    fromBits (multiply (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 0 evalTinySigned.emin_lsb))
        (encodeValue (f := evalTinySigned) .posInf)
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

-- Division follows D1's explicit NaN, zero, and infinity rows.
example :
    fromBits (divide (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .nan)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

example :
    fromBits (divide (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .posInf)
        (encodeValue (f := evalTinySigned) .negInf)
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

example :
    fromBits (divide (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        (encodeValue (f := evalTinySigned) (.finite 0 evalTinySigned.emin_lsb))
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

example :
    fromBits (divide (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        (encodeValue (f := evalTinySigned) .posInf)
        RoundingMode.RNE SaturationMode.SatNone) =
      Value.finite 0 evalTinySigned.emin_lsb := by
  native_decide

-- Unary operations project their mathematical result, including for unsigned formats.
example :
    fromBits (negate (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 0 evalTinySigned.emin_lsb))
        RoundingMode.RNE SaturationMode.SatNone) =
      Value.finite 0 evalTinySigned.emin_lsb := by
  native_decide

example :
    fromBits (negate (f := evalTinyUnsignedFin)
        (encodeValue (f := evalTinyUnsignedFin)
          (.finite 1 evalTinyUnsignedFin.emin_lsb))
        RoundingMode.RNE SaturationMode.SatFinite) =
      Value.finite 0 evalTinyUnsignedFin.emin_lsb := by
  native_decide

example :
    fromBits (absProject (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .nan)
        RoundingMode.RNE SaturationMode.SatNone) = Value.nan := by
  native_decide

-- Comparisons involving NaN are false; minimum and maximum propagate NaN.
example :
    isLess (f := evalTinySigned)
      (encodeValue (f := evalTinySigned) .nan)
      (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb)) = false := by
  native_decide

example :
    isGreater (f := evalTinySigned)
      (encodeValue (f := evalTinySigned) .nan)
      (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb)) = false := by
  native_decide

example :
    isEqual (f := evalTinySigned)
      (encodeValue (f := evalTinySigned) .nan)
      (encodeValue (f := evalTinySigned) .nan) = false := by
  native_decide

example :
    fromBits (minimum (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) .nan)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))) =
      Value.nan := by
  native_decide

example :
    fromBits (maximum (f := evalTinySigned)
        (encodeValue (f := evalTinySigned) (.finite 1 evalTinySigned.emin_lsb))
        (encodeValue (f := evalTinySigned) .nan)) = Value.nan := by
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
