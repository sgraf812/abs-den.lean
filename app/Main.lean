import AbsDen.Basic
-- import AbsDen.Semantics
import AbsDen.Repro

--instance : Repr ((T.F (Heap (▹ D) × Value))^[10] Unit) where
--  reprPrec := @reprPrec _ (@instReprIterate _ 10 Unit (fun β inst => @T.instReprF (Heap (▹ D) × Value) β _ inst) _)

-- #eval takeT 10 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})

def main : IO Unit :=
  -- IO.println (repr (takeT 10 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})))
  IO.println "hi"
