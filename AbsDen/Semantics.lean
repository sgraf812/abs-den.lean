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
-- protected def T.noConfusionType.{u,u_1} {α : Type u} (P : Sort u_1) (v1 : T α) (v2 : T α) : Sort u_1 :=
--   T.F.noConfusionType P (cast T.unfold v1) (cast T.unfold v2)
-- protected def T.noConfusion.{u_1, u} {α : Type u} {P : Sort u_1} {v1 v2 : T α} (h12 : v1 = v2) : T.noConfusionType P v1 v2 :=
--   T.F.noConfusion (v1 := cast T.unfold v1) (v2 := cast T.unfold v2) (congrArg (cast T.unfold) h12)
@[match_pattern]
def T.ret (x : α) : T α := cast T.unfold.symm (T.F.ret x)
@[match_pattern]
def T.step (e : Event) (tl : ▹ T α) : T α := cast T.unfold.symm (T.F.step e (cast DLater.next_eq tl))
protected def T.recOn.{v,u} {α : Type u} {motive : T α  → Sort v} (t : T α)
  (ret : (a : α) → motive (T.ret a))
  (step : (e : Event) → (tl : ▹ T α) → motive (T.step e tl))
  : motive t := by
    let motive2 : T.F α (next[]. T α) → Sort v := motive ∘ cast T.unfold.symm
    let fw {t} : motive (cast T.unfold.symm t) → motive2 t := cast rfl
    let bw {t} : motive2 (cast T.unfold t) → motive t      := cast (congrArg motive (by simp))
    have h : motive2 (cast T.unfold t) :=
      let go : (t : T.F α (next[]. T α)) → motive2 t
             | .ret a     => fw (ret a)
             | .step e tl => cast (by simp) (fw (step e (cast DLater.next_eq.symm tl)))
      go (cast T.unfold t)
    exact bw h
theorem T.ne_ret_step : ¬ (T.ret a = T.step e tl) := by unfold T.ret T.step; simp
theorem T.confuse_ret : T.ret a1 = T.ret a2 → a1 = a2 := by unfold T.ret; simp
theorem T.confuse_step1 : T.step e1 tl1 = T.step e2 tl2 → e1 = e2 := by unfold T.step; simp; intro a b; exact a
theorem T.confuse_step2 : T.step e1 tl1 = T.step e2 tl2 → tl1 = tl2 := by unfold T.step; simp

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

def ByNeed.mk (f : Heap (next[]. D) → T (Heap (next[]. D) × α)) : ByNeed α := ByNeed.F.mk f
def ByNeed.f (d : ByNeed α) : Heap (next[]. D) → T (Heap (next[]. D) × α) := match d with | ByNeed.F.mk f => f
@[simp]
def ByNeed.mk_f {f : Heap (next[]. D) → T (Heap (next[]. D) × α)} : (ByNeed.mk f).f = f := by unfold ByNeed.mk ByNeed.f; simp
@[simp]
def ByNeed.f_mk {d : ByNeed α} : ByNeed.mk d.f = d := by unfold ByNeed.mk ByNeed.f; simp
theorem ByNeed.ext {d₁ d₂ : ByNeed α} (h : d₁.f = d₂.f) : d₁ = d₂ := by
  calc d₁ = ByNeed.mk (d₁.f) := rfl
       _  = ByNeed.mk (d₂.f) := by rw[h]
       _  = d₂               := rfl

def D.mk (f : Heap (next[]. D) → T (Heap (next[]. D) × Value)) : D := ByNeed.mk f
def D.f (d : D) := @ByNeed.f Value d

--@[simp]
--theorem cast_stuff {α β : Type u} {h : α = β} {a b : α} (h2 : cast h a = cast h b) : a = b :=
--  (cast_inj h).mp h2

@[simp]
theorem D.mk_f {f} : (D.mk f).f = f := by unfold D.mk D.f; simp
@[simp]
theorem D.f_mk {d} : D.mk d.f = d := by unfold D.mk D.f; simp
theorem D.ext {d₁ d₂ : D} (h : d₁.f = d₂.f) : d₁ = d₂ := by
  calc d₁ = D.mk d₁.f := by simp
       _  = D.mk d₂.f := by rw[h]
       _  = d₂        := by simp

def D.step (e : Event) (tl : ▹ D) : D := D.mk fun μ => T.step e (next[d ← tl]. d.f μ)
@[simp]
theorem D.step_f : (D.step e tl).f μ = T.step e (next[d ← tl]. d.f μ) := by unfold D.step; simp

set_option trace.simps.debug true in
instance : Trace D where
  step := D.step

theorem EnvD.property_f (d : EnvD D) (μ : Heap (next[]. D)) :
  ∃ (x:Name) (tl: ▹ D), d.val.f μ = step (Event.look x) (next[d' : D ← tl]. d'.f μ)
:= by
  have ⟨x,tl,h⟩ := d.property
  exact ⟨x,tl, by rw[h]; exact D.step_f⟩

protected def EnvD.proj_pre (τ : T (Heap (next[]. D) × Value)) (μ : Heap (next[]. D)) :
  Prop := ∃ (x:Name) (tl: ▹ D), τ = step (Event.look x) (next[d' : D ← tl]. d'.f μ)

def EnvD.name (d : EnvD D) : Name :=
  (d.val.f {}).recOn (motive:= fun τ => (EnvD.proj_pre τ {}) -> Name)
    (fun a h => absurd h (fun ⟨x,tl,h⟩ => T.ne_ret_step h))
    (fun e tl h => by
      cases e
      case look x => exact x
      repeat' (absurd h; rcases h with ⟨x,tl,h⟩; have h := T.confuse_step1 h; nomatch h))
    (d.property_f {})

def EnvD.tl (d : EnvD D) : ▹ D :=
  let f (μ : Heap _) : ▹ (T (Heap _ × Value)) :=
    (d.val.f μ).recOn (motive:= fun τ => (EnvD.proj_pre τ μ) -> ▹ (T (Heap _ × Value)))
      (fun a h => absurd h (fun ⟨x,tl,h⟩ => T.ne_ret_step h))
      (fun e tl h => by
        cases e
        case look x => exact tl
        repeat' (absurd h; rcases h with ⟨x,tl,h⟩; have h := T.confuse_step1 h; nomatch h))
      (d.property_f μ)
  (cast D.eq.symm ∘ @ByNeed.mk Value) <$> Later.flip2 f

theorem EnvD.iso (d : EnvD D) : d.val = step (Event.look d.name) d.tl := by
  funext by
  calc d.val μ = _ := rfl
       _     = step (Event.look d.name) d.tl μ := sorry

instance : Monad ByNeed where
  pure a := ByNeed.mk fun μ => T.ret ⟨μ, a⟩
  bind a k := ByNeed.mk fun μ => a.f μ >>= fun
    | ⟨μ₂, r⟩ => ByNeed.f (k r) μ₂

instance : Domain D isEnv where
  stuck := cast D.eq.symm <| pure Value.stuck
  fn _x f := cast D.eq.symm <| pure (Value.fun (fun x d => f ⟨step (Event.look x) d, _, _, rfl⟩))
  ap d a := cast D.eq.symm do
    let v ← cast D.eq d
    cast a.property.2.2 a.val
    let ⟨_,hp⟩ := a
    match v with
    | .fun f => f x d
    | _      => stuck
