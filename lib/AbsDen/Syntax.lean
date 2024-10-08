import Mathlib.Data.List.AList
import Mathlib.Order.CompleteLattice

abbrev FinMap k v := AList (λ (_ : k) => v)

notation f "[" k "↦" v "]" => AList.replace k v f

def FinMap.map [DecidableEq k] (f : a → b) (m : FinMap k a) : FinMap k b := Id.run do
  let mut res := {}
  for ⟨k,v⟩ in m.entries do
    res := res[k↦f v]
  pure res

def FinMap.unionWith [DecidableEq k] (merge : v → v → v) (l : FinMap k v) (r : FinMap k v) : FinMap k v := Id.run do
  let mut res := l
  for ⟨k,rv⟩ in r.entries do
    match AList.lookup k l with
    | .none    => res := res[k↦rv]
    | .some lv => res := res[k↦merge lv rv]
  pure res

instance [CompleteLattice v] : CompleteLattice (FinMap k v) := sorry

abbrev Name := String
-- abbrev ConTag := Nat

inductive Exp where
  | var : Name → Exp
  | app : Exp → Name → Exp
  | lam : Name → Exp → Exp
  | let : Name → Exp → Exp → Exp
--  | con : ConTag → List Name → Exp
--  | select : Exp → FinMap ConTag (List Name × Exp) → Exp
  deriving Repr

-- instance : DecidableEq Name := String.decEq

declare_syntax_cat exp
syntax:max ident : exp
syntax "(" exp ")" : exp
syntax:arg exp:arg ident : exp
syntax:max "fun" ident+ " => " exp:arg : exp
syntax:max "let" ident " := " exp "; " exp : exp
syntax "[exp|" exp "|]" : term

open Lean in
macro_rules
  | `([exp| ($e) |]) => `([exp| $e |])
  | `([exp| $x:ident |]) => `(Exp.var $(quote x.getId.toString))
  | `([exp| $e $x |]) => `(Exp.app [exp| $e |] $(quote x.getId.toString))
  | `([exp| fun $x => $e |]) => `(Exp.lam $(quote x.getId.toString) [exp| $e |])
  | `([exp| fun $x $y $ys => $e |]) => `(Exp.lam $(quote x.getId.toString) [exp| fun $y $ys => $e |])
  | `([exp| let $x := $e1; $e2 |]) => `(Exp.let $(quote x.getId.toString) [exp| $e1 |] [exp| $e2 |])

example := [exp| let id := fun x => x; id id |]
