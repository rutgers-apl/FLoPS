import Flops.P3109.Exec.Value

open p3109_format
open p3109_format.Exec

private def formats : List (String × p3109_format) := [
  ("Binary4p1se", ⟨4, 1, .signed, .extended, by decide, by decide⟩),
  ("Binary4p2se", ⟨4, 2, .signed, .extended, by decide, by decide⟩),
  ("Binary4p3se", ⟨4, 3, .signed, .extended, by decide, by decide⟩),
  ("Binary4p1sf", ⟨4, 1, .signed, .finite, by decide, by decide⟩),
  ("Binary4p2sf", ⟨4, 2, .signed, .finite, by decide, by decide⟩),
  ("Binary4p3sf", ⟨4, 3, .signed, .finite, by decide, by decide⟩),
  ("Binary4p1ue", ⟨4, 1, .unsigned, .extended, by decide, by decide⟩),
  ("Binary4p2ue", ⟨4, 2, .unsigned, .extended, by decide, by decide⟩),
  ("Binary4p3ue", ⟨4, 3, .unsigned, .extended, by decide, by decide⟩),
  ("Binary4p4ue", ⟨4, 4, .unsigned, .extended, by decide, by decide⟩),
  ("Binary4p1uf", ⟨4, 1, .unsigned, .finite, by decide, by decide⟩),
  ("Binary4p2uf", ⟨4, 2, .unsigned, .finite, by decide, by decide⟩),
  ("Binary4p3uf", ⟨4, 3, .unsigned, .finite, by decide, by decide⟩),
  ("Binary4p4uf", ⟨4, 4, .unsigned, .finite, by decide, by decide⟩)
]

private def valueToken {f : p3109_format} (bits : Bits f) : String :=
  match fromBits bits with
  | .nan => "nan"
  | .posInf => "+inf"
  | .negInf => "-inf"
  | .finite 0 _ => "zero"
  | .finite m e => s!"finite:{m}:{e}"

private def tableRow (name : String) (f : p3109_format) : String :=
  let values := (List.finRange (2 ^ f.K)).map valueToken
  String.intercalate " " (name :: values)

def main : IO Unit :=
  formats.forM fun (name, f) => IO.println (tableRow name f)
