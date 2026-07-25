import Flops.P3109.Exec.Defs
import Flops.P3109.Exec.Decode

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace p3109_format
namespace Exec

def packFiniteMagnitude (f : p3109_format) (fields : FiniteFields f) : Nat :=
  fields.exponentField * exponentModulus f + fields.trailingField

def packPositiveFinite (f : p3109_format) (fields : FiniteFields f) : Nat :=
  packFiniteMagnitude f fields

def packNegativeFinite (f : p3109_format) (fields : FiniteFields f) : Nat :=
  packFiniteMagnitude f fields + signBase f

/--
Executable codec from decoded values to bit-level code points.
-/
def encodeFinite (f : p3109_format) (fields : FiniteFields f) : Nat :=
  if _hs : f.s = .signed then
    if fields.sign then packNegativeFinite f fields else packPositiveFinite f fields
  else
    packPositiveFinite f fields

def encodeSpecial (f : p3109_format) (d : Decoded f) : Nat :=
  match d with
  | .nan => nanCode f
  | .posInf =>
    if f.s = .signed then signBase f - 1 else maxCode f - 1
  | .negInf => maxCode f
  | .finite fields => encodeFinite f fields

def encode (x : Decoded f) : Bits f :=
  let n := encodeSpecial f x
  ⟨n % 2 ^ f.K, by
    exact Nat.mod_lt _ (pow_pos (Nat.succ_pos 1) f.K)⟩

def encodeNat (x : Decoded f) : Nat :=
  encodeSpecial f x

def encodeExact (x : Decoded f) (h : encodeNat x < 2 ^ f.K) : Bits f :=
  ⟨encodeNat x, h⟩

lemma encode_decode_eq (x : Bits f) : encodeNat (decode x) = x := by
  by_cases hnan : (x : Nat) = nanCode f
  · have henc : encodeSpecial f Decoded.nan = nanCode f := by
      simp [encodeSpecial]
    simpa [decode, encodeNat, hnan, henc]
  · cases hs : f.s with
    | signed =>
      cases hd : f.d with
      | finite =>
        by_cases hpos : posInfCode? f = some (x : Nat)
        · exfalso
          simpa [posInfCode?, hs, hd] using hpos
        · by_cases hneg : negInfCode? f = some (x : Nat)
          · exfalso
            simpa [negInfCode?, hs, hd] using hneg
          · by_cases hreg : negativeRegion f x = true
            · have hsign : signBase f < (x : Nat) := by
                simpa [negativeRegion, hs] using hreg
              have hmod : (↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f = ↑x - signBase f := by
                exact Nat.div_add_mod' (↑x - signBase f) (exponentModulus f)
              have hsign' : signBase f ≤ (x : Nat) := Nat.le_of_lt hsign
              have hx' : signBase f + ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f) = (x : Nat) := by
                calc
                  signBase f + ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f)
                      = signBase f + (↑x - signBase f) := by simp [hmod]
                  _ = (↑x - signBase f) + signBase f := by omega
                  _ = (x : Nat) := Nat.sub_add_cancel hsign'
              have hx : ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f) + signBase f = (x : Nat) := by
                simpa [Nat.add_comm] using hx'
              simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packNegativeFinite, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using hx
            · simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using
                (Nat.div_add_mod' (↑x) (exponentModulus f))
      | extended =>
        by_cases hpos : posInfCode? f = some (x : Nat)
        · have hx : (x : Nat) = signBase f - 1 := by
            simpa [eq_comm, posInfCode?, hs, hd] using hpos
          have hdec : decode x = Decoded.posInf := by
            simp [decode, hs, hd, hpos, hnan]
          have henc : encodeNat (decode x) = signBase f - 1 := by
            have hspec : encodeSpecial f Decoded.posInf = signBase f - 1 := by
              simp [encodeSpecial, hs]
            simpa [encodeNat, hdec, hspec]
          simpa [hx] using henc
        · by_cases hneg : negInfCode? f = some (x : Nat)
          · have hx : (x : Nat) = maxCode f := by
              simpa [eq_comm, negInfCode?, hs, hd] using hneg
            have hdec : decode x = Decoded.negInf := by
              simp [decode, hs, hd, hpos, hneg, hnan]
            have henc : encodeNat (decode x) = maxCode f := by
              have hspec : encodeSpecial f Decoded.negInf = maxCode f := by
                simp [encodeSpecial]
              simpa [encodeNat, hdec, hspec]
            simpa [hx] using henc
          · by_cases hreg : negativeRegion f x = true
            · have hsign : signBase f < (x : Nat) := by
                simpa [negativeRegion, hs] using hreg
              have hmod : (↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f = ↑x - signBase f := by
                exact Nat.div_add_mod' (↑x - signBase f) (exponentModulus f)
              have hsign' : signBase f ≤ (x : Nat) := Nat.le_of_lt hsign
              have hx' : signBase f + ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f) = (x : Nat) := by
                calc
                  signBase f + ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f)
                      = signBase f + (↑x - signBase f) := by simp [hmod]
                  _ = (↑x - signBase f) + signBase f := by omega
                  _ = (x : Nat) := Nat.sub_add_cancel hsign'
              have hx : ((↑x - signBase f) / exponentModulus f * exponentModulus f + (↑x - signBase f) % exponentModulus f) + signBase f = (x : Nat) := by
                simpa [Nat.add_comm] using hx'
              simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packNegativeFinite, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using hx
            · simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using
                (Nat.div_add_mod' (↑x) (exponentModulus f))
    | unsigned =>
      cases hd : f.d with
      | finite =>
        by_cases hpos : posInfCode? f = some (x : Nat)
        · exfalso
          simpa [posInfCode?, hs, hd] using hpos
        · by_cases hneg : negInfCode? f = some (x : Nat)
          · exfalso
            simpa [negInfCode?, hs, hd] using hneg
          · by_cases hreg : negativeRegion f x = true
            · exfalso
              simpa [negativeRegion, hs] using hreg
            · simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using
                (Nat.div_add_mod' (↑x) (exponentModulus f))
      | extended =>
        by_cases hpos : posInfCode? f = some (x : Nat)
        · have hx : (x : Nat) = maxCode f - 1 := by
            simpa [eq_comm, posInfCode?, hs, hd] using hpos
          have hdec : decode x = Decoded.posInf := by
            simp [decode, hs, hd, hpos, hnan]
          have henc : encodeNat (decode x) = maxCode f - 1 := by
            have hspec : encodeSpecial f Decoded.posInf = maxCode f - 1 := by
              simp [encodeSpecial, hs]
            simpa [hdec, encodeNat, hspec]
          simpa [hx] using henc
        · by_cases hneg : negInfCode? f = some (x : Nat)
          · exfalso
            simpa [negInfCode?, hs, hd] using hneg
          · by_cases hreg : negativeRegion f x = true
            · exfalso
              simpa [negativeRegion, hs] using hreg
            · simpa [decode, encodeNat, encodeSpecial, encodeFinite, packFiniteMagnitude, packPositiveFinite, finiteFieldsOfMagnitude, hs, hd, hnan, hpos, hneg, hreg] using
                (Nat.div_add_mod' (↑x) (exponentModulus f))

lemma encode_lt_of_decode (x : Bits f) : encodeNat (decode x) < 2 ^ f.K := by
  have h : encodeNat (decode x) = x := encode_decode_eq x
  exact h ▸ x.isLt

def reencode (x : Bits f) : Bits f :=
  encodeExact (decode x) (encode_lt_of_decode x)

lemma reencode_eq (x : Bits f) : reencode x = x := by
  apply Fin.ext
  exact encode_decode_eq x

end Exec
end p3109_format
