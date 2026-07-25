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

example :
    ∀ x y : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (divide (f := tinySignedNarrow) x y rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow (toEReal (fromBits x) / toEReal (fromBits y)) rnd sat) := by
  intro x y rnd sat
  simpa using
    (div_refines (f := tinySignedNarrow) x y rnd sat )

example :
    ∀ x y : Bits tinySignedExtended,
    ∀ rnd sat,
    toEReal (fromBits (divide (f := tinySignedExtended) x y rnd sat ))
      = (@p3109_format.p3109.project tinySignedExtended (toEReal (fromBits x) / toEReal (fromBits y)) rnd sat) := by
  intro x y rnd sat
  simpa using
    (div_refines (f := tinySignedExtended) x y rnd sat )

-- Project/reproject and arithmetic semantic checks through the executable
-- projection pipeline.
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

example :
    ∀ x y : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (add (f := tinySignedNarrow) x y rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          (toEReal (fromBits x) + toEReal (fromBits y)) rnd sat) := by
  intro x y rnd sat
  simpa using (add_refines (f := tinySignedNarrow) x y rnd sat )

example :
    ∀ x y : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (subtract (f := tinySignedNarrow) x y rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          (toEReal (fromBits x) - toEReal (fromBits y)) rnd sat) := by
  intro x y rnd sat
  simpa using
    (subtract_refines (f := tinySignedNarrow) x y rnd sat )

example :
    ∀ x y : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal (fromBits (multiply (f := tinySignedNarrow) x y rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          (toEReal (fromBits x) * toEReal (fromBits y)) rnd sat) := by
  intro x y rnd sat
  simpa using
    (multiply_refines (f := tinySignedNarrow) x y rnd sat )

example :
    ∀ x y z : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal
        (fromBits (fma (f := tinySignedNarrow) x y z rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          (toEReal (fromBits x) * toEReal (fromBits y) + toEReal (fromBits z))
          rnd sat) := by
  intro x y z rnd sat
  simpa using
    (fma_refines (f := tinySignedNarrow) x y z rnd sat )

example :
    ∀ x y z : Bits tinySignedNarrow,
    ∀ rnd sat,
    toEReal
        (fromBits (faa (f := tinySignedNarrow) x y z rnd sat ))
      = (@p3109_format.p3109.project tinySignedNarrow 
          ((toEReal (fromBits x) + toEReal (fromBits y)) + toEReal (fromBits z))
          rnd sat) := by
  intro x y z rnd sat
  simpa using
    (faa_refines (f := tinySignedNarrow) x y z rnd sat )

-- Comparison and extrema refinements.
example :
    ∀ x y : Bits tinySignedNarrow,
    isEqual (f := tinySignedNarrow) x y = decide (x = y) := by
  intro x y
  simpa using (isEqual_refines (f := tinySignedNarrow) x y)

example :
    ∀ x y : Bits tinyUnsignedNarrow,
    toEReal (fromBits (minimum (f := tinyUnsignedNarrow) x y))
      = (if (toEReal (fromBits x)) < (toEReal (fromBits y))
        then toEReal (fromBits x) else toEReal (fromBits y)) := by
  intro x y
  simpa using (minimum_refines (f := tinyUnsignedNarrow) x y)

example :
    ∀ x y : Bits tinyUnsignedExtended,
    toEReal (fromBits (maximum (f := tinyUnsignedExtended) x y))
      = (if (toEReal (fromBits y)) < (toEReal (fromBits x))
        then toEReal (fromBits x) else toEReal (fromBits y)) := by
  intro x y
  simpa using (maximum_refines (f := tinyUnsignedExtended) x y)

example :
    ∀ x y : Bits tinyUnsignedExtended,
    toEReal (fromBits (minimum (f := tinyUnsignedExtended) x y))
      = (if (toEReal (fromBits x)) < (toEReal (fromBits y))
        then toEReal (fromBits x) else toEReal (fromBits y)) := by
  intro x y
  simpa using (minimum_refines (f := tinyUnsignedExtended) x y)

end Exec
end p3109_format
