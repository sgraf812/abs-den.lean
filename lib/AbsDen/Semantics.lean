import AbsDen.Syntax

inductive Event where
  | look : Name → Event
  | upd | app1 | app2 | let1 | case1 | case2
  deriving Repr

class Trace (D : Type) (L : outParam (Type → Type)) where
  step : Event → L D → D
abbrev isStep [Trace D L] (d : D) (ev : Event) : Prop :=
  ∃ (d' : L D), d = Trace.step ev d'
abbrev isEnv [Trace D L] (d : D) : Prop :=
  ∃ (y : Name), isStep d (Event.look y)
abbrev EnvD D [Trace D L] := Subtype (@isEnv D _ _)

class Domain (D : Type) (L : outParam (Type → Type)) extends Trace D L where
  stuck : D
  fn : (Subtype (@isEnv D _ _) → D) → D
  ap : D → Subtype (@isEnv D _ _) → D
--  con : ConTag → List d → d
--  select : d → AList ConTag (List d → d) → d

class HasBind (d : Type) (L : outParam (Type → Type)) where
  bind : Name → (L d → d) → (L d → d) → d

def eval {D : Type} {L : outParam (Type → Type)} [Applicative L] [Domain D L] [HasBind D L] (e : Exp) (ρ : FinMap Name (EnvD D)) : D :=
match e with
  | Exp.var x => if _ : x ∈ ρ then ρ[x] else Domain.stuck
  | Exp.lam x e => Domain.fn (λ d => Trace.step Event.app2 (pure (eval e (ρ[x↦d]))))
  | Exp.app e x => if _ : x ∈ ρ then Trace.step Event.app1 (pure (Domain.ap (eval e ρ) ρ[x])) else Domain.stuck
  | Exp.let x e₁ e₂ => HasBind.bind x (λ d₁ => eval e₁ (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))
                                      (λ d₁ => Trace.step Event.let1 (pure (eval e₂ (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))))

def evalK {D : Type} {L : outParam (Type → Type)} [Applicative L] [Domain D L] [HasBind D L] (K : LContext) (S : FinMap Name (EnvD D) -> D) (ρ : FinMap Name (EnvD D)) : D :=
match K with
  | LContext.hole => S ρ
  | LContext.lam x K => Domain.fn (λ d => Trace.step Event.app2 (pure (evalK K S (ρ[x↦d]))))
  | LContext.app K x => match AList.lookup x ρ with
      | Option.none   => Domain.stuck
      | Option.some d => Trace.step Event.app1 (pure (Domain.ap (evalK K S ρ) d))
  | LContext.let_body x e K => HasBind.bind x (λ d₁ => eval e (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))
                                              (λ d₁ => Trace.step Event.let1 (pure (evalK K S (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))))
  | LContext.let_rhs x K e => HasBind.bind x (λ d₁ => evalK K S (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))
                                             (λ d₁ => Trace.step Event.let1 (pure (eval e (ρ[x↦⟨Trace.step (Event.look x) d₁, _, _, rfl⟩]))))
