import AbsDen.Syntax

inductive Event where
  | look : Name → Event
  | upd | app1 | app2 | let1 | case1 | case2
  deriving Repr

class Trace (L : Type → Type) (d : Type) where
  step : Event → L d → d

abbrev isEnv L δ [Trace L δ] (d : δ) : Prop :=
  ∃ (y : Name) (d' : L δ), d = Trace.step (Event.look y) d'
abbrev EnvD L d [Trace L d] := Subtype (isEnv L d)

class Domain (d : Type) (p : d → Prop) where
  stuck : d
  fn : Name → (Subtype p → d) → d
  ap : d → Subtype p → d
--  con : ConTag → List d → d
--  select : d → AList ConTag (List d → d) → d

class HasBind (L : Type → Type) (d : Type) where
  bind : Name → (L d → d) → (L d → d) → d

abbrev isEnv.stuck {d : Type} [Trace L d] [Domain d (isEnv L d)] : d := @Domain.stuck d (isEnv L d) _

def eval [Trace L d] [Applicative L] [Domain d (isEnv L d)] [HasBind L d] (ρ : FinMap Name (EnvD L d)) : Exp → d
  | Exp.var x => match AList.lookup x ρ with
      | Option.none   => isEnv.stuck (L:=L)
      | Option.some d => d
  | Exp.lam x e => Domain.fn x (λ d => Trace.step (L:=L) Event.app2 (pure (eval (ρ[x↦d]) e)))
  | Exp.app e x => match AList.lookup x ρ with
      | Option.none   => isEnv.stuck (L:=L)
      | Option.some d => Trace.step (L:=L) Event.app1 (pure (Domain.ap (eval ρ e) d))
  | Exp.let x e₁ e₂ => HasBind.bind x (λ d₁ => eval (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]) e₁)
                                      (λ d₁ => Trace.step (L:=L) Event.let1 (pure (eval (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]) e₂)))
