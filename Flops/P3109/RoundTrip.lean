import Flops.P3109.Rounding
import Flops.P3109.Projection

namespace p3109_format
namespace p3109

lemma rt {f : p3109_format} {x : p3109 f} :
  @encode f (@to_cereal f x) (by simp [to_cereal, value_set]) = x := by
  generalize_proofs at *;
  cases x;
  · cases ‹Bool› <;> aesop;
  · exact?;
  · rename_i m e hm h;
    convert finite_encode_self _ _;
    · unfold p3109.to_cereal p3109.to_ereal; aesop;
    · exact?;
    · convert h using 1

noncomputable def to_cereal' {f : p3109_format}
  (x : p3109 f) :
  {x : EReal ⊕ Unit // x ∈ (value_set f)} :=
  ⟨@to_cereal f x, by simp [value_set]⟩

lemma bi2 {f : p3109_format} : Function.Bijective (@to_cereal' f) := by
  constructor
  simp [Function.Injective]
  intro a b heq
  simp [to_cereal'] at heq
  rw [<-rt (x:=a)]
  rw [<-rt (x:=b)]
  simp_rw [heq]
  unfold Function.Surjective
  rintro ⟨x, ⟨p, hpx⟩⟩
  exists p; simp [to_cereal', hpx]
