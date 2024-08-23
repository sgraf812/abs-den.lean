import AbsDen.Syntax
import AbsDen.IGDTT
import Mathlib.Data.List.AList

open IGDTT

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

inductive T.F (α : Type) (τ : ▹ Type) : Type where
  | ret : α → T.F α τ
  | step : Event → ▸ τ → T.F α τ
def T α := T.F α (gfix (T.F α))

inductive Value.Tag : Type where
  | stuck
  | fun
def Value.F (d : ▹ Type) : Type := @Sigma Value.Tag fun
  | .stuck => unit
  | .fun   => (Name × ▸ d → T (Value.F d))
inductive ValueF (d : ▹ Type) : Type where
  | stuck : ValueF d
  | fun : (Name × ▸ d → T (ValueF d)) → ValueF d
  --  | con : Con → List (Name × ▸ d) → ValueF d

def Value := ValueF (gfix (T ∘ ValueF))
def D := T Value
