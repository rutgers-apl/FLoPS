-- This module serves as the root of the `Flops` library.
-- Import modules here that should be built as part of the library.
-- correctness guarantee
import Flops.P3109.Bijection
import Flops.P3109.RoundTrip
-- Rounding properties
import Flops.P3109.RtoProperty
import Flops.P3109.StochasticProperties
import Flops.P3109.RoundingProjection
-- Arithmetic properties
import Flops.P3109.Sterbenz
import Flops.P3109.Fast2Sum
import Flops.P3109.Fast2SumSat
import Flops.P3109.Scalar
--
import Flops.P3109.KApproximate
import Lean

def tofile : IO Unit := do
  let filePath : System.FilePath := "example.txt"
  let handle ← IO.FS.Handle.mk filePath .append
  let f : p3109_format := ⟨4, 3, .signed, .finite, by simp, by simp⟩
  /-
  for i in [:16] do
    let x := @p3109_format.p3109.n_to_p3109 f ⟨i, by sorry⟩

    IO.FS.Handle.putStrLn handle (toString x)
  -/
def main : IO Unit := do
  tofile
