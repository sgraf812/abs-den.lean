import IGDTT
import AbsDen.Semantics
import Mathlib.Data.List.MinMax

open IGDTT

inductive T.F (α : Type u) (τ : Type u) : Type u where
  | ret : α → T.F α τ
  | step : Event → τ → T.F α τ
  deriving Repr
def T α := gfix (fun τ => T.F α (▸ τ))
theorem T.unfold : T α = T.F α (▹ T α) := calc
  T α = T.F α (▸ next[]. T α) := gfix.unfold (fun τ => T.F α (▸ τ))
  _   = T.F α (▹ T α) := by rw[DLater.next_eq]
@[match_pattern]
def T.ret (x : α) : T α := cast T.unfold.symm (T.F.ret x)
@[match_pattern]
def T.step (e : Event) (tl : ▹ T α) : T α := cast T.unfold.symm (T.F.step e tl)
protected def T.recOn.{v,u} {α : Type u} {motive : T α  → Sort v} (t : T α)
  (ret : (a : α) → motive (T.ret a))
  (step : (e : Event) → (tl : ▹ T α) → motive (T.step e tl))
  : motive t := by
    let motive2 : T.F α (▹ T α) → Sort v := motive ∘ cast T.unfold.symm
    let bw {t} : motive2 (cast T.unfold t) → motive t := cast (congrArg motive (by simp))
    have h : motive2 (cast T.unfold t) :=
      let go : (t : T.F α (▹ T α)) → motive2 t
             | .ret a     => ret a
             | .step e tl => step e tl
      go (cast T.unfold t)
    exact bw h

@[simp]
protected theorem T.F.recOn_cast.{v,u} {α : Type u} {τ} {motive : T.F α τ  → Sort v} {r s t} (h : T.F α τ = β)
  : (cast h.symm (cast h t)).recOn (motive:=motive) r s
  = cast (congrArg motive (by simp : t = cast h.symm (cast h t))) (t.recOn (motive:=motive) r s)
  := by cases h; rfl
@[simp]
protected theorem T.recOn_cast.{v,u} {α : Type u} {motive : T α  → Sort v} {r s t} (h : T α = β)
  : (cast h.symm (cast h t)).recOn (motive:=motive) r s
  = cast (congrArg motive (by simp : t = cast h.symm (cast h t))) (t.recOn (motive:=motive) r s)
  := by cases h; rfl
protected theorem T.recOn_rw.{v,u} {α : Type u} {motive : T α  → Sort v} {r s τ1 τ2} (h : τ1 = τ2)
  : τ1.recOn (motive:=motive) r s
  = cast (congrArg motive h.symm) (τ2.recOn (motive:=motive) r s)
  := by cases h; rfl
@[simp]
protected theorem T.recOn_ret.{v,u} {α : Type u} {motive : T α  → Sort v} {a r s}
  : (T.ret a).recOn (motive:=motive) r s = r a := by
  unfold T.recOn recOn.match_1 T.ret
  simp
@[simp]
protected theorem T.recOn_step.{v,u} {α : Type u} {motive : T α  → Sort v} {e tl r s}
  : (T.step e tl).recOn (motive:=motive) r s = s e tl := by
  unfold T.recOn recOn.match_1 T.step
  simp
theorem T.ne_ret_step : ¬ (T.ret a = T.step e tl) := by unfold T.ret T.step; simp
theorem T.confuse_ret : T.ret a1 = T.ret a2 → a1 = a2 := by unfold T.ret; simp
theorem T.confuse_step1 : T.step e1 tl1 = T.step e2 tl2 → e1 = e2 := by unfold T.step; simp_all
theorem T.confuse_step2 : T.step e1 tl1 = T.step e2 tl2 → tl1 = tl2 := by unfold T.step; simp

def T.bind {α β} (t : T α) (k : α → T β) : T β :=
  let loop loop' t : T β := match cast T.unfold t with
    | .ret a     => k a
    | .step e tl => T.step e (next[loop ← loop', t ← tl]. loop t)
  gfix loop t

instance instTraceT : Trace (T α) Later where
  step := T.step

instance : Monad T where
  pure := T.ret
  bind := T.bind

-- Convention: p is the inductive recursion variable, n is the guarded one.
--             So ultimately, p will be instantiated with D, while n will be instantiated with ▹ D.
abbrev Heap (n : Type) := FinMap Nat n
structure ByNeed.F (n : Type) (α : Type) : Type where
  mk :: f : Heap n → T (Heap n × α)

inductive Value.F (p : Type) (n : Type) : Type where
  | stuck : Value.F p n
  | fun : (Name → n → p) → Value.F p n
-- trustMeFix is safe for any monotone `f`
partial def trustMeFix [Nonempty α] (f : α → α) := f (trustMeFix f)
axiom trustMeFix.unfold {α} [Nonempty α] (f : α → α) : trustMeFix f = f (trustMeFix f)
-- axiom trustMeFix.ind {α} [Nonempty α] {f : α → α} {g : α → α} : ((x:α) → f x = g x) → trustMeFix f = trustMeFix g
-- axiom trustMeFix.fixpoint {α} [Nonempty α] {f : α → α} {x : α} : (f x = x) → trustMeFix f = x
-- the functional below is clearly monotone because p only occurs in positive position,
-- so D.F is a proper inductive datatype.
abbrev D.F (p : Type) (n : Type) := ByNeed.F n (Value.F p n)
def D := gfix (fun n => trustMeFix (fun p => D.F p (▸ n)))
theorem D.unfold : D = D.F D (▹ D) := by
  calc D = gfix (fun n => trustMeFix (fun p => D.F p (▸ n))) := rfl
       _ = trustMeFix (fun p => D.F p (▸ (next[]. D))) := gfix.unfold _
       _ = D.F (trustMeFix (fun p => D.F p (▸ (next[]. D)))) (▸ (next[]. D)) := trustMeFix.unfold _
       _ = D.F (trustMeFix (fun p => D.F p (▸ (next[]. D)))) (▹ D) := by rw[DLater.next_eq]
       _ = D.F D (▹ D) := congrArg (D.F · (▹ D)) (gfix.unfold (fun n => trustMeFix (fun p => D.F p (▸ n)))).symm
instance : Coe D (D.F D (▹ D)) where
  coe := cast D.unfold
instance : Coe (D.F D (▹ D)) D where
  coe := cast D.unfold.symm

abbrev Value := Value.F D (▹ D)
abbrev Value.stuck : Value := Value.F.stuck
abbrev Value.fun (f : Name → ▹ D → D) : Value := Value.F.fun f

abbrev ByNeed α := ByNeed.F (▹ D) α

theorem D.eq : D = ByNeed Value := by
  calc D = D.F D (▹ D) := D.unfold
       _ = ByNeed Value := rfl
instance : Coe D (ByNeed Value) where
  coe := cast D.eq
instance : Coe (ByNeed Value) D where
  coe := cast D.eq.symm

def ByNeed.mk (f : Heap (▹ D) → T (Heap (▹ D) × α)) : ByNeed α := ByNeed.F.mk f
def ByNeed.f (d : ByNeed α) : Heap (▹ D) → T (Heap (▹ D) × α) := match d with | ByNeed.F.mk f => f
@[simp]
def ByNeed.mk_f {f : Heap (▹ D) → T (Heap (▹ D) × α)} : (ByNeed.mk f).f = f := by unfold ByNeed.mk ByNeed.f; simp
@[simp]
def ByNeed.f_mk {d : ByNeed α} : ByNeed.mk d.f = d := by unfold ByNeed.mk ByNeed.f; simp
theorem ByNeed.ext {d₁ d₂ : ByNeed α} (h : d₁.f = d₂.f) : d₁ = d₂ := by
  calc d₁ = ByNeed.mk (d₁.f) := rfl
       _  = ByNeed.mk (d₂.f) := by rw[h]
       _  = d₂               := rfl

def D.mk (f : Heap (▹ D) → T (Heap (▹ D) × Value)) : D := ByNeed.mk f
def D.f (d : D) := @ByNeed.f Value d
@[simp]
theorem D.mk_f {f} : (D.mk f).f = f := by unfold D.mk D.f; simp
@[simp]
theorem D.f_mk {d} : D.mk d.f = d := by unfold D.mk D.f; simp
theorem D.ext {d₁ d₂ : D} (h : d₁.f = d₂.f) : d₁ = d₂ := by
  calc d₁ = D.mk d₁.f := by simp
       _  = D.mk d₂.f := by rw[h]
       _  = d₂        := by simp

def D.ret (v : Value) : D := D.mk fun μ => T.ret ⟨μ, v⟩
@[simp]
theorem D.ret_f : (D.ret v).f μ = T.ret ⟨μ, v⟩ := by unfold D.ret; simp
def D.step (e : Event) (tl : ▹ D) : D := D.mk fun μ => T.step e (next[d ← tl]. d.f μ)
@[simp]
theorem D.step_f : (D.step e tl).f μ = T.step e (next[d ← tl]. d.f μ) := by unfold D.step; simp

instance instTraceD : Trace D Later where
  step := D.step

theorem EnvD.property_f (d : EnvD D) (μ : Heap (▹ D)) :
  ∃ (x:Name) (tl: ▹ D), d.val.f μ = T.step (Event.look x) (next[d' : D ← tl]. d'.f μ)
:= by
  have ⟨x,tl,h⟩ := d.property
  exact ⟨x,tl, by rw[h]; exact D.step_f⟩

protected def EnvD.proj_pre (τ : T (Heap (▹ D) × Value)) (μ : Heap (▹ D)) :
  Prop := ∃ (x:Name) (tl: ▹ D), τ = T.step (Event.look x) (next[d' : D ← tl]. d'.f μ)

def EnvD.name (d : EnvD D) : Name :=
  (d.val.f {}).recOn (motive:= fun τ => (EnvD.proj_pre τ {}) -> Name)
    (fun a h => absurd h (fun ⟨x,tl,h⟩ => T.ne_ret_step h))
    (fun e tl h => by
      cases e
      case look x => exact x
      repeat' (absurd h; rcases h with ⟨x,tl,h⟩; have h := T.confuse_step1 h; nomatch h))
    (d.property_f {})

def EnvD.tl (d : EnvD D) : ▹ D :=
  next[f ← Later.unsafeFlip fun μ =>
    (d.val.f μ).recOn (motive:= fun τ => (EnvD.proj_pre τ μ) -> ▹ (T (Heap _ × Value)))
      (fun a h => absurd h (fun ⟨x,tl,h⟩ => T.ne_ret_step h))
      (fun e tl h => by
        cases e
        case look x => exact tl
        repeat' (absurd h; rcases h with ⟨x,tl,h⟩; have h := T.confuse_step1 h; nomatch h))
      (d.property_f μ)]. D.mk f

@[simp]
theorem help3 {f : α₁ → β₁} {a : α₂} (h₁ : α₁ = α₂) (h₂ : β₁ = β₂) :
  (cast (Eq.trans (congrArg (· → β₁) h₁) (congrArg (α₂ → ·) h₂)) f) a = cast h₂ (f (cast h₁.symm a))
:= by
  cases h₁
  cases h₂
  rfl

@[simp]
theorem help {a : α} (h : β = α) : (cast (congrArg (· → γ) h) f) a = f (cast h.symm a) := by simp[help3 h rfl]

@[simp]
theorem help2 {a : γ} (h : β = α) : (cast (congrArg (γ → ·) h) f) a = cast h (f a) := by simp[help3 rfl h]

theorem EnvD.iso (d : EnvD D) : d.val = D.step (Event.look d.name) d.tl := D.ext <| funext fun μ => by
  --unfold EnvD.name
  --simp
  have ⟨x, tl, h⟩ := d.property
  have hμ := congrArg (fun d => d.f μ) h
  have hemp := congrArg (fun d => d.f {}) h
  simp[instTraceD] at *
  have hx : x = d.name := by
    unfold EnvD.name
    rw[T.recOn_rw hemp]
    rw[help3 (by unfold EnvD.proj_pre; simp[hemp]) rfl]
    simp
  have htl : tl = d.tl := by
    unfold EnvD.tl
    simp
    sorry
  -- This is hard and tedious to prove, and perhaps utlimately unnecessary. Postpone
  --  unfold instApplicativeLater D.mk
  --  rw[Later.unsafeFlip_eq]
  --  set_option trace.Meta.Tactic.simp true in
  --  simp only[(T.recOn_rw hμ)]
  rw[hμ, hx, htl]

instance : Monad ByNeed where
  pure a := ByNeed.mk fun μ => T.ret ⟨μ, a⟩
  bind a k := ByNeed.mk fun μ => a.f μ >>= fun
    | ⟨μ₂, r⟩ => ByNeed.f (k r) μ₂

instance : Domain D Later where
  stuck := cast D.eq.symm <| pure Value.stuck
  fn f := cast D.eq.symm <| pure (Value.fun (fun x d => f ⟨Trace.step (Event.look x) d, _, _, rfl⟩))
  ap d a := cast D.eq.symm do
    let v ← cast D.eq d
    match v with
    | .fun f => f (EnvD.name a) (EnvD.tl a)
    | _      => pure Value.stuck

abbrev is_allocator (f : Heap (▹ D) → Nat) := ∀ μ, f μ ∉ μ

def nextFree (μ : Heap (▹ D)) : Nat := match μ.keys.maximum? with
| .none => 0
| .some n => n+1

theorem nextFree_is_allocator : is_allocator nextFree := by
  intro μ
  rw[AList.mem_keys]
  unfold nextFree
  split
  · simp_all
  · next n h =>
    have h := (List.maximum?_le_iff (by simp) h n).mp Nat.le.refl
    intro (habsurd : n+1 ∈ μ.keys)
    have h : n+1 ≤ n := h (n+1) habsurd
    omega

def fetch (a : Nat) : ▹ D :=
  next[f ← Later.unsafeFlip fun (μ : Heap (▹ D)) =>
    match AList.lookup a μ with
    | .some ld => next[d ← ld]. d.f μ
    | .none    => next[]. T.ret ⟨μ, Value.stuck⟩]. D.mk f

def stepLookFetch (x : Name) (a : Nat) : D :=
  D.mk fun μ =>
    match AList.lookup a μ with
    | .some ld => Trace.step (Event.look x) (next[d ← ld]. d.f μ)
    | .none    => Trace.step (Event.look x) (next[]. T.ret ⟨μ, Value.stuck⟩)

-- the following theorem is important to get rid of the unsafeFlip in fetch:
theorem stepLook_fetch_eq_stepLookFetch
  : Trace.step (Event.look x) (fetch a) = stepLookFetch x a
:= D.ext <| by
  unfold instTraceD D.step fetch stepLookFetch
  ext μ
  simp[Later.ap.assoc2]
  rw[Later.unsafeFlip_eq]
  split <;> simp[Trace.step, instTraceT]

def memo (a : Nat) : ▹ D → ▹ D :=
  gfix fun lmemo ld => next[d ← ld, memo ← lmemo]. cast D.eq.symm do
    let v ← cast D.eq d
    ByNeed.mk fun μ =>
      let μ' := μ[a↦memo (next[]. cast D.eq.symm <| pure v)]
      T.step Event.upd (next[]. T.ret ⟨μ', v⟩)

def get : ByNeed (Heap (▹ D)) := ByNeed.mk fun μ => T.ret ⟨μ,μ⟩
def put (μ : Heap (▹ D)) : ByNeed Unit := ByNeed.mk fun _ => T.ret ⟨μ,⟨⟩⟩

instance : HasBind D Later where
  bind _x rhs body := cast D.eq.symm do
    let μ ← get
    let a := nextFree μ
    put (μ[a ↦ memo a (next[]. rhs (fetch a))])
    body (fetch a)

instance : Applicative Later where
  pure a := Later.next (fun () => a)
  seq f a := Later.ap f (a ())

def evalByNeed : FinMap Name (EnvD D) → Exp → D := eval

def takeT (n : Nat) (t : T α) : (T.F α)^[n] Unit := match n, cast T.unfold t with
| 0, _ => ()
| .succ _, .ret a => cast (Function.iterate_succ_apply' _ _ _).symm (T.F.ret a)
| .succ n, .step e lt => cast (Function.iterate_succ_apply' _ _ _).symm (T.F.step e (takeT n (Later.unsafeForce lt)))

instance : Repr (Value.F p n) where
  reprPrec v _ := match v with
  | .stuck => "stuck"
  | .fun _ => "fun"

instance : Repr (Heap (▹ D)) where
  reprPrec μ n := reprPrec μ.keys n

class C (n : Nat) where
  m : Nat

-- instance : C n where
--   m :=

instance instReprIterate (f : Type → Type) (n : Nat) (α : Type) [instReprF : ∀β [Repr β], Repr (f β)] [instReprα : Repr α] : Repr (f^[n] α) where
  reprPrec t p := match n with
  | 0   => reprPrec (cast (by simp : f^[0] α = α) t) p
  | n+1 => let t := (cast (Function.iterate_succ_apply' _ _ _ : f^[n+1] α = f (f^[n] α)) t);
           @reprPrec _ (@instReprF _ (@instReprIterate _ _ _ instReprF _)) t p

-- #synth Repr ((T.F (Heap (▹ D) × Value))^[100] Unit)
-- #eval takeT 100 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})
