import AbsDen.Syntax
import AbsDen.IGDTT
import Mathlib.Data.List.AList

open IGDTT

inductive Event where
  | look : Name → Event
  | upd | app1 | app2 | let1 | case1 | case2

class Trace (d : Type) where
  step : Event → ▹ d → d
open Trace

class Domain (a : Type) (d : Type) where
  stuck : d
  fn : Name → (a → d) → d
  ap : d → a → d
--  con : ConTag → List d → d
--  select : d → AList ConTag (List d → d) → d
open Domain

class HasBind (d : Type) where
  bind : Name → (d → d) → (d → d) → d
open HasBind

def eval [Trace d] [Domain d d] [HasBind d] (ρ : FinMap Name d) : Exp → d
  | Exp.var x => match AList.lookup x ρ with
      | Option.none   => @stuck d _ _
      | Option.some d => d
  | Exp.lam x e => fn x (λ d => step Event.app2 (next[]. eval (ρ[x↦d]) e))
  | Exp.app e x => match AList.lookup x ρ with
      | Option.none   => @stuck d _ _
      | Option.some d => step Event.app1 (next[]. ap (eval ρ e) d)
  | Exp.let x e₁ e₂ => bind x (λ d₁ =>                          eval (ρ[x↦step (Event.look x) (next[]. d₁)]) e₁)
                              (λ d₁ => step Event.let1 (next[]. eval (ρ[x↦step (Event.look x) (next[]. d₁)]) e₂))

inductive T.F (α : Type u) (τ : ▹ (Type u)) : Type u where
  | ret : α → T.F α τ
  | step : Event → ▸ τ → T.F α τ
def T α := gfix (T.F α)
theorem T.unfold : T α = T.F α (next[]. T α) := gfix.unfold (T.F α)
instance : Coe (T α) (T.F α (next[]. T α)) where
  coe := cast T.unfold
instance : Coe (T.F α (next[]. T α)) (T α) where
  coe := cast T.unfold.symm
def T.ret (x : α) : T α := cast T.unfold.symm (T.F.ret x)
def T.step (e : Event) (tl : ▹ T α) : T α := cast T.unfold.symm (T.F.step e (cast DLater.next_eq tl))
protected def T.recOn.{v,u} {α : Type u} {motive : T α  → Sort v} (t : T α)
  (ret : (a : α) → motive (T.ret a))
  (step : (e : Event) → (tl : ▹ T α) → motive (T.step e tl))
  : motive t := by
    let motive2 : T.F α (next[]. T α) → Sort v := motive ∘ cast T.unfold.symm
    let fw {t} : motive (cast T.unfold.symm t) → motive2 t := cast (by aesop)
    let bw {t} : motive2 (cast T.unfold t) → motive t := cast (by aesop)
    have h : motive2 (cast T.unfold t) :=
      let go : (t : T.F α (next[]. T α)) → motive2 t
             | .ret a     => fw (ret a)
             | .step e tl => cast (by aesop) (fw (step e (cast DLater.next_eq.symm tl)))
      go (cast T.unfold t)
    exact bw h
def T.bind {α β} (t : T α) (k : α → T β) : T β :=
  let loop loop' t : T β := match cast T.unfold t with
    | .ret a     => k a
    | .step e tl => T.step e (next[loop ← loop', t ← cast DLater.next_eq.symm tl]. loop t)
  gfix loop t

instance : Trace (T α) where
  step := T.step

instance : Monad T where
  pure := T.ret
  bind := T.bind

def Heap (n : ▹ Type) := Nat → ▸ n
structure ByNeed.F (d : ▹ Type) (α : Type) : Type where
  mk :: f : Heap d → T (Heap d × α)

inductive Value.F (p : Type) (n : ▹ Type) : Type where
  | stuck : Value.F p n
  | fun : (▸ n → p) → Value.F p n
-- trustMeFix is safe for any monotone `f`
partial def trustMeFix [Nonempty α] (f : α → α) := f (trustMeFix f)
axiom trustMeFix.unfold {α} [Nonempty α] (f : α → α) : trustMeFix f = f (trustMeFix f)
-- axiom trustMeFix.ind {α} [Nonempty α] {f : α → α} {g : α → α} : ((x:α) → f x = g x) → trustMeFix f = trustMeFix g
-- axiom trustMeFix.fixpoint {α} [Nonempty α] {f : α → α} {x : α} : (f x = x) → trustMeFix f = x
-- the functional below is clearly monotone because p only occurs in positive position,
-- so D.F is a proper inductive datatype.
def D.F (p : Type) (n : ▹ Type) := ByNeed.F n (Value.F p n)
def D := gfix (fun n => trustMeFix (fun p => D.F p n))
theorem D.unfold : D = D.F D (next[].D) := by
  calc D = gfix (fun n => trustMeFix (fun p => D.F p n)) := rfl
       _ = trustMeFix (fun p => D.F p (next[]. D)) := gfix.unfold _
       _ = D.F (trustMeFix (fun p => D.F p (next[]. D))) (next[]. D) := trustMeFix.unfold _
       _ = D.F D (next[].D) := congrArg (D.F · (next[]. D)) (gfix.unfold (fun n => trustMeFix (fun p => D.F p n))).symm
instance : Coe D (D.F D (next[]. D)) where
  coe := cast D.unfold
instance : Coe (D.F D (next[]. D)) D where
  coe := cast D.unfold.symm

abbrev Value := Value.F D (next[].D)
def Value.stuck : Value := Value.F.stuck
def Value.fun (f : ▹ D → D) : Value := Value.F.fun (f ∘ cast DLater.next_eq.symm)

abbrev ByNeed α := ByNeed.F (next[]. D) α

theorem D.eq : D = ByNeed Value := by
  calc D = D.F D (next[].D) := D.unfold
       _ = ByNeed Value := rfl
instance : Coe D (ByNeed Value) where
  coe := cast D.eq
instance : Coe (ByNeed Value) D where
  coe := cast D.eq.symm

def ByNeed.mk (f : Heap (next[]. D) → T (Heap (next[]. D) × α)) : ByNeed α :=
  ByNeed.F.mk f
def ByNeed.f (d : ByNeed α) : Heap (next[]. D) → T (Heap (next[]. D) × α) :=
  match d with | ByNeed.F.mk f => f

abbrev D.f (d : D) := @ByNeed.f Value d
abbrev D.bv : ByNeed Value → D := cast D.eq.symm
abbrev D.unBv : ByNeed Value → D := cast D.eq.symm

instance : Trace D where
  step e tl := ByNeed.mk fun μ => step e (next[d ← tl]. d.f μ)

instance : Monad ByNeed where
  pure a := ByNeed.mk fun μ => T.ret ⟨μ, a⟩
  bind a k := ByNeed.mk fun μ => a.f μ >>= fun
    | ⟨μ₂, r⟩ => ByNeed.f (k r) μ₂

instance : Domain (▹ D) D where
  stuck := D.mk <| pure Value.stuck
  fn f := D.mk <| pure (Value.fun f)
  ap d a := D.mk do
    let v ← d
    match v with
    | .fun f => f a
    | _      => stuck
