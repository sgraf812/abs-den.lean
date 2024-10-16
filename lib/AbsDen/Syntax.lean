import Mathlib.Data.List.AList
import Mathlib.Order.CompleteLattice

abbrev FinMap k v := AList (λ (_ : k) => v)

notation:max f "[" k "↦" v "]" => AList.replace k v f

def FinMap.map [DecidableEq k] (f : a → b) (m : FinMap k a) : FinMap k b := Id.run do
  let mut res := {}
  for ⟨k,v⟩ in m.entries do
    res := res[k↦f v]
  pure res

def FinMap.map_with_key [DecidableEq k] (f : k → a → b) (m : FinMap k a) : FinMap k b := Id.run do
  let mut res := {}
  for ⟨k,v⟩ in m.entries do
    res := res[k↦f k v]
  pure res
theorem FinMap.dom_map_with_key [DecidableEq key] {k : key} {f : key → a → b} {m : FinMap key a} :
    k ∈ m ↔ k ∈ map_with_key f m := sorry

def FinMap.unionWith [DecidableEq k] (merge : v → v → v) (l : FinMap k v) (r : FinMap k v) : FinMap k v := Id.run do
  let mut res := l
  for ⟨k,rv⟩ in r.entries do
    match AList.lookup k l with
    | .none    => res := res[k↦rv]
    | .some lv => res := res[k↦merge lv rv]
  pure res

instance [CompleteLattice v] : CompleteLattice (FinMap k v) := sorry
instance instFinMapGetElem [DecidableEq k] : GetElem (FinMap k v) k v Membership.mem where
  getElem m k h := match AList.lookup k m, AList.lookup_isSome.mpr h with
  | .some v, _ => v

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

abbrev Exp.is_value (e : Exp) : Prop := ∃ x, ∃ e₁, e = Exp.lam x e₁

inductive LContext where
| hole : LContext
| app : LContext → Name → LContext
| lam : Name → LContext → LContext
| let_body : Name → Exp → LContext → LContext
| let_rhs : Name → LContext → Exp → LContext
deriving Repr

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
  | `([exp| fun $x $ys => $e |]) => `(Exp.lam $(quote x.getId.toString) [exp| fun $ys => $e |])
  | `([exp| let $x := $e1; $e2 |]) => `(Exp.let $(quote x.getId.toString) [exp| $e1 |] [exp| $e2 |])

example := [exp| let id := fun x => x; id id |]
example := [exp| let id := (fun x y => y) id; id |]

declare_syntax_cat ctx
syntax:max "□" : ctx
syntax "(" ctx ")" : ctx
syntax:arg ctx:arg ident : ctx
syntax:max "fun" ident+ " => " ctx:arg : ctx
syntax:max "let" ident " := " ctx "; " exp : ctx
syntax:max "let" ident " := " exp "; " ctx : ctx
syntax "[ctx|" ctx "|]" : term

open Lean in
macro_rules
  | `([ctx| ($K) |]) => `([ctx| $K |])
  | `([ctx| □ |]) => `(LContext.hole)
  | `([ctx| $K $x |]) => `(LContext.app [ctx| $K |] $(quote x.getId.toString))
  | `([ctx| fun $x => $K |]) => `(LContext.lam $(quote x.getId.toString) [ctx| $K |])
  | `([ctx| fun $x $ys => $K |]) => `(LContext.lam $(quote x.getId.toString) [ctx| fun $ys => $K |])
  | `([ctx| let $x := $K:ctx; $e:exp |]) => `(LContext.let_rhs $(quote x.getId.toString) [ctx| $K |] [exp| $e |])
  | `([ctx| let $x := $e:exp; $K:ctx |]) => `(LContext.let_body $(quote x.getId.toString) [exp| $e |] [ctx| $K |])

example := [ctx| let id := fun x => x; (fun x => □ id) |]
example := [ctx| let id := fun x => □; (fun x => id) |]
