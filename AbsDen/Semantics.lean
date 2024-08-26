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

class Domain (d : Type) (p : d → Prop) where
  stuck : d
  fn : Name → (Subtype p → d) → d
  ap : d → Subtype p → d
--  con : ConTag → List d → d
--  select : d → AList ConTag (List d → d) → d
open Domain

class HasBind (d : Type) (p : d → Prop) where
  bind : Name → (▹Subtype p → Subtype p) → (▹Subtype p → d) → d
open HasBind

abbrev isEnv {δ : Type} [Trace δ] (d : δ) : Prop :=
  ∃ y d', d = step (Event.look y) d'
abbrev isEnv.stuck {d : Type} [Trace d] [Domain d isEnv] : d := @Domain.stuck d (@isEnv d _) _
abbrev EnvD (d : Type) [Trace d] := Subtype (@isEnv d _)

def eval [Trace d] [Domain d isEnv] [HasBind d isEnv] (ρ : FinMap Name (EnvD d)) : Exp → d
  | Exp.var x => match AList.lookup x ρ with
      | Option.none   => isEnv.stuck
      | Option.some d => d
  | Exp.lam x e => fn x (λ d => step Event.app2 (next[]. eval (ρ[x↦d]) e))
  | Exp.app e x => match AList.lookup x ρ with
      | Option.none   => isEnv.stuck
      | Option.some d => step Event.app1 (next[]. ap (eval ρ e) d)
  | Exp.let x e₁ e₂ => bind x (λ dd₁ => ⟨step (Event.look x) (next[d₁:EnvD d ← dd₁]. eval (ρ[x↦d₁]) e₁), _, _, rfl⟩)
                              (λ dd₁ => step Event.let1     (next[d₁ ← dd₁]. eval (ρ[x↦d₁]) e₂))

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

abbrev Heap (n : ▹ Type) := FinMap Nat (▸ n)
structure ByNeed.F (d : ▹ Type) (α : Type) : Type where
  mk :: f : Heap d → T (Heap d × α)

inductive Value.F (p : Type) (n : ▹ Type) : Type where
  | stuck : Value.F p n
  | fun : (Name → ▸ n → p) → Value.F p n
-- trustMeFix is safe for any monotone `f`
partial def trustMeFix [Nonempty α] (f : α → α) := f (trustMeFix f)
axiom trustMeFix.unfold {α} [Nonempty α] (f : α → α) : trustMeFix f = f (trustMeFix f)
-- axiom trustMeFix.ind {α} [Nonempty α] {f : α → α} {g : α → α} : ((x:α) → f x = g x) → trustMeFix f = trustMeFix g
-- axiom trustMeFix.fixpoint {α} [Nonempty α] {f : α → α} {x : α} : (f x = x) → trustMeFix f = x
-- the functional below is clearly monotone because p only occurs in positive position,
-- so D.F is a proper inductive datatype.
abbrev D.F (p : Type) (n : ▹ Type) := ByNeed.F n (Value.F p n)
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
abbrev Value.stuck : Value := Value.F.stuck
abbrev Value.fun (f : Name → ▹ D → D) : Value := Value.F.fun (fun n => f n ∘ cast DLater.next_eq.symm)

abbrev ByNeed α := ByNeed.F (next[]. D) α

theorem D.eq : D = ByNeed Value := by
  calc D = D.F D (next[].D) := D.unfold
       _ = ByNeed Value := rfl
instance : Coe D (ByNeed Value) where
  coe := cast D.eq
instance : Coe (ByNeed Value) D where
  coe := cast D.eq.symm

set_option trace.simps.debug true in
@[simps]
def ByNeed.mk (f : Heap (next[]. D) → T (Heap (next[]. D) × α)) : ByNeed α :=
  ByNeed.F.mk f
#check ByNeed.mk_f

def ByNeed.f (d : ByNeed α) : Heap (next[]. D) → T (Heap (next[]. D) × α) :=
  match d with | ByNeed.F.mk f => f

def D.f (d : D) := @ByNeed.f Value d
def D.need : ByNeed Value → D := cast D.eq.symm
def D.unNeed : D → ByNeed Value := cast D.eq

instance : Trace D where
  step e tl := ByNeed.mk fun μ => step e (next[d ← tl]. d.f μ)

theorem EnvD.thing (d : EnvD D) (μ : Heap (next[]. D)) :
  ∃ x t, cast T.unfold (d.val.f μ) = T.F.step (Event.look x) (cast DLater.next_eq t)
:= by
  have ⟨x,tl,h⟩ := d.property
  apply Exists.intro x
  apply Exists.intro (next[d ← tl]. d.f μ)

  calc cast _ (d.val.f μ) = cast T.unfold ((step (Event.look x) tl).f μ) := by rw[h]
       _                  = T.F.step (Event.look x) _ := rfl
       _                  = cast T.unfold (step (Event.look x) (next[d ← tl]. d.f μ)) := by
         unfold step cast
         simp
         trivial
       _                  = T.F.step (Event.look x) (cast DLater.next_eq (next[d ← tl]. d.f μ)) := by
         unfold step cast
         set_option trace.Elab.step true in
         trivial

def EnvD.name [Trace D] (d : EnvD D) : Name := match cast T.unfold (d.val.f {}) with
  | T.F.step (Event.look x) _ => x
  | _ => absurd d.property sorry
def EnvD.d' [Trace D] (d : EnvD D) : ▹ D :=
  let f (μ : Heap _) : ▹ (T (Heap _ × Value)):= match cast T.unfold (d.val.f μ) with
  | T.F.step _ d => cast DLater.next_eq.symm d
  | _            => sorry
  (cast D.eq.symm ∘ @ByNeed.mk Value) <$> Later.flip2 f

instance : Monad ByNeed where
  pure a := ByNeed.mk fun μ => T.ret ⟨μ, a⟩
  bind a k := ByNeed.mk fun μ => a.f μ >>= fun
    | ⟨μ₂, r⟩ => ByNeed.f (k r) μ₂

instance : Domain D isEnv where
  stuck := D.eq.symm ▸ pure Value.stuck
  fn _x f := D.eq.symm ▸ pure (Value.fun (fun x d => f ⟨step (Event.look x) d, _, _, rfl⟩))
  ap d a := D.eq.symm ▸ do
    let v ← D.eq ▸ d
    cast a.property.2.2 a.val
    let ⟨_,hp⟩ := a
    match v with
    | .fun f => f x d
    | _      => stuck
