import AbsDen.Syntax
import Mathlib.Data.List.AList

inductive Event where
  | look : Name → Event
  | upd | app1 | app2 | let1 | case1 | case2

class Trace (d : Type) where
  step : Event → d → d
open Trace

class Domain (d : Type) where
  stuck : d
  fn : Name → (d → d) → d
  ap : d → d → d
--  con : ConTag → List d → d
--  select : d → AList ConTag (List d → d) → d
open Domain

class HasBind (d : Type) where
  bind : Name → (d → d) → (d → d) → d
open HasBind

def eval [Trace d] [Domain d] [HasBind d] (ρ : FinMap Name d) : Exp → d
  | Exp.var x => match AList.lookup x ρ with
      | Option.none   => stuck
      | Option.some d => d
  | Exp.lam x e => fn x (λ d => step Event.app2 (eval (ρ[x↦d]) e))
  | Exp.app e x => match AList.lookup x ρ with
      | Option.none   => stuck
      | Option.some d => step Event.app1 (ap (eval ρ e) d)
  | Exp.let x e₁ e₂ => bind x (λ d₁ =>                  eval (ρ[x↦step (Event.look x) d₁]) e₁)
                              (λ d₁ => step Event.let1 (eval (ρ[x↦step (Event.look x) d₁]) e₂))

inductive T : Nat → Type where
  | ret : T n
  | step : Event → T n → T (n+1)
inductive Value : Nat → Type where
  | stuck : Value n
  | fun : (Value n → Value n) → Value (n+1)
--  | con : ConTag →
