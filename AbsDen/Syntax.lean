import Mathlib.Data.List.AList

def FinMap k v := AList (λ (_ : k) => v)

notation f "[" k "↦" v "]" => AList.replace k v f

def Name := String
-- def ConTag := Nat

inductive Exp where
  | var : Name → Exp
  | app : Exp → Name → Exp
  | lam : Name → Exp → Exp
  | let : Name → Exp → Exp → Exp
--  | con : ConTag → List Name → Exp
--  | select : Exp → FinMap ConTag (List Name × Exp) → Exp

instance : DecidableEq Name := String.decEq
