import AbsDen.Basic
import AbsDen.Semantics
import AbsDen.ByNeed
import IGDTT
-- import AbsDen.Repro

open IGDTT

instance : Repr ((T.F (Heap (▹ D) × Value))^[5] Unit) where
  reprPrec := @reprPrec _ (@instReprIterate _ 5 Unit (fun β inst => @T.instReprF (Heap (▹ D) × Value) β _ inst) _)

-- #eval takeT 10 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})

def NatStream : Type := gfix (fun r => Nat × ▸ r)
theorem NatStream.unfold : NatStream = (Nat × ▹ NatStream) := calc
  NatStream = (Nat × ▸ (next[]. NatStream)) := gfix.unfold (fun s => Nat × ▸ s)
  _         = (Nat × ▹ NatStream) := by rw[DLater.next_eq]

def ones : NatStream := gfix (fun s => cast NatStream.unfold.symm ⟨1, s⟩)

def takeS (n : Nat) (s : NatStream) : List Nat := match n with
| 0 => []
| n+1 => let ⟨k,s'⟩ := cast NatStream.unfold s; k :: takeS n (Later.unsafeForce s')

-- #eval takeS 10 ones

def apps : D := gfix (fun s => D.step Event.app1 s)

def main : IO Unit := do
  IO.println "before"
  IO.println (Later.unsafeForce (Later.next (fun () => 42)))
  IO.println (Later.unsafeForce (next[]. 23))
  IO.println (Later.unsafeForce (next[f ← next[]. id, a ← next[].12]. f a))
  IO.println (takeS 10 ones)
  IO.println (Later.unsafeForce (next[blah ← next[]. id, g ← Later.unsafeFlip (fun f => next[]. f 23)]. g blah))
  IO.println (repr (takeT 5 (apps.f {})))
  IO.println "between"
  -- IO.println (repr (takeT 5 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})))
  -- IO.println (repr (takeT 5 ((evalByNeed {} (Exp.let "id" (Exp.lam "x" (Exp.var "x")) (Exp.var "id"))).f {})))
  IO.println "after"
