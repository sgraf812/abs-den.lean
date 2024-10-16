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
@[simp]
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
@[simp]
theorem T.step_eq : T.step e₁ tl₁ = T.step e₂ tl₂ ↔ e₁ = e₂ ∧ tl₁ = tl₂ := by
  unfold T.step; simp_all

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

theorem T.confuse_pure : instMonadT.pure a = instMonadT.pure b → a = b := by
  unfold pure instMonadT; simp; exact T.confuse_ret

@[simp]
theorem D.step_eq : instTraceT.step e₁ tl₁ = instTraceT.step e₂ tl₂ ↔ e₁ = e₂ ∧ tl₁ = tl₂ := by
  unfold Trace.step instTraceT; simp

-- Convention: p is the inductive recursion variable, n is the guarded one.
--             So ultimately, p will be instantiated with D, while n will be instantiated with ▹ D.
abbrev Heap.F (n : Type) := FinMap Nat n
structure ByNeed.F (n : Type) (α : Type) : Type where
  mk :: f : Heap.F n → T (Heap.F n × α)
abbrev Addr := Nat

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

abbrev Heap := Heap.F (▹ D)
abbrev Value := Value.F D (▹ D)
abbrev Value.stuck : Value := Value.F.stuck
abbrev Value.fun (f : Name → ▹ D → D) : Value := Value.F.fun f
theorem Value.confuse_fun : Value.fun f₁ = Value.fun f₂ → f₁ = f₂ := by intro h; injection h
theorem Value.ne_stuck_fun : Value.fun f ≠ Value.stuck := by intro h; injection h

abbrev ByNeed α := ByNeed.F (▹ D) α

theorem D.eq : D = ByNeed Value := by
  calc D = D.F D (▹ D) := D.unfold
       _ = ByNeed Value := rfl
instance : Coe D (ByNeed Value) where
  coe := cast D.eq
instance : Coe (ByNeed Value) D where
  coe := cast D.eq.symm

def ByNeed.mk (f : Heap → T (Heap × α)) : ByNeed α := ByNeed.F.mk f
def ByNeed.f (d : ByNeed α) : Heap → T (Heap × α) := match d with | ByNeed.F.mk f => f
@[simp]
def ByNeed.mk_f {f : Heap → T (Heap × α)} : (ByNeed.mk f).f = f := by unfold ByNeed.mk ByNeed.f; simp
@[simp]
def ByNeed.f_mk {d : ByNeed α} : ByNeed.mk d.f = d := by unfold ByNeed.mk ByNeed.f; simp
theorem ByNeed.ext {d₁ d₂ : ByNeed α} (h : d₁.f = d₂.f) : d₁ = d₂ := by
  calc d₁ = ByNeed.mk (d₁.f) := rfl
       _  = ByNeed.mk (d₂.f) := by rw[h]
       _  = d₂               := rfl

def D.mk (f : Heap → T (Heap × Value)) : D := ByNeed.mk f
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
def D.step (e : Event) (tl : ▹ D) : D := D.mk fun μ => T.step e (next[d ← tl]. d.f μ)

instance instTraceD : Trace D Later where
  step := D.step
instance : Inhabited D where default := D.ret Value.stuck

@[simp]
theorem D.step_f : (Trace.step e tl).f μ = Trace.step e (next[d:D ← tl]. d.f μ) := by
  unfold Trace.step instTraceD instTraceT D.step; simp

theorem EnvD.property_f (d : EnvD D) (μ : Heap) :
  ∃ (x:Name) (tl: ▹ D), d.val.f μ = Trace.step (Event.look x) (next[d' : D ← tl]. d'.f μ)
:= by
  have ⟨x,tl,h⟩ := d.property
  exact ⟨x,tl, by rw[h]; exact D.step_f⟩

protected def EnvD.proj_pre (τ : T (Heap × Value)) (μ : Heap) :
  Prop := ∃ (x:Name) (tl: ▹ D), τ = Trace.step (Event.look x) (next[d' : D ← tl]. d'.f μ)

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
    (d.val.f μ).recOn (motive:= fun τ => (EnvD.proj_pre τ μ) -> ▹ (T (Heap × Value)))
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

@[simp]
theorem EnvD.iso (d : EnvD D) : d.val = Trace.step (Event.look d.name) d.tl := D.ext <| funext fun μ => by
  --unfold EnvD.name
  --simp
  have ⟨x, tl, h⟩ := d.property
  have hμ := congrArg (fun d => d.f μ) h
  have hemp := congrArg (fun d => d.f {}) h
  have hx : x = d.name := by
    unfold EnvD.name
    rw[T.recOn_rw hemp]
    rw[T.recOn_rw D.step_f]
    unfold Trace.step instTraceT EnvD.proj_pre
    simp
    rw[help (f := fun h => x)]
    rw[h]
    unfold Trace.step instTraceT instTraceD D.step
    simp
  have htl : tl = d.tl := by
    unfold EnvD.tl
    simp
    apply Later.ext
    simp
    -- This is hard and tedious to prove, and perhaps utlimately unnecessary. Postpone
    --  unfold instApplicativeLater D.mk
    --  set_option trace.Meta.Tactic.simp true in
    --rw[D.ext]
    --rw[Later.unsafeFlip_eq]
    --unfold instApplicativeLater D.mk
    sorry
  rw[h, hx, htl]

instance instMonadByNeed : Monad ByNeed where
  pure a := ByNeed.mk fun μ => T.ret ⟨μ, a⟩
  bind a k := ByNeed.mk fun μ => a.f μ >>= fun
    | ⟨μ₂, r⟩ => ByNeed.f (k r) μ₂

@[simp]
theorem ByNeed.pure_f : (pure v : ByNeed α).f μ = pure ⟨μ, v⟩ := by
  unfold pure instMonadByNeed instMonadT; simp

@[simp]
theorem D.pure_f : (cast D.eq.symm m).f μ = m.f μ := by unfold D.f; simp

theorem ByNeed.confuse_pure : instMonadByNeed.pure a = instMonadByNeed.pure b → a = b := by
  unfold pure instMonadByNeed ByNeed.mk; simp;
  intro h
  let μ : Heap := default
  have : (μ,a) = (μ,b) := by
    apply T.confuse_ret
    exact congrFun h μ
  injection this

instance instDomainD : Domain D Later where
  stuck := cast D.eq.symm <| pure Value.stuck
  fn f := cast D.eq.symm <| pure (Value.fun (fun x d => f ⟨Trace.step (Event.look x) d, _, _, rfl⟩))
  ap d a := cast D.eq.symm do
    let v ← cast D.eq d
    match v with
    | .fun f => f (EnvD.name a) (EnvD.tl a)
    | _      => pure Value.stuck

theorem D.confuse_fn : instDomainD.fn f₁ = instDomainD.fn f₂ → f₁ = f₂ := by
  unfold Domain.fn instDomainD; simp;
  intro h
  ext d
  obtain ⟨_,x,d,hd⟩ := d
  cases hd
  exact congrFun (congrFun (Value.confuse_fun (ByNeed.confuse_pure h)) x) d

theorem D.confuse_fn_heap : (instDomainD.fn f₁).f μ₁ = (instDomainD.fn f₂).f μ₂ → μ₁ = μ₂ := by
  unfold Domain.fn instDomainD; simp;
  intro h
  have := T.confuse_pure h
  injection this

@[simp]
theorem D.ne_stuck_fn : instDomainD.stuck.f μ₁ ≠ (instDomainD.fn g).f μ₂ := by
  unfold Domain.stuck Domain.fn instDomainD
  simp
  intro h
  have := T.confuse_pure h
  simp_all

@[simp]
theorem D.ne_step_fn : instTraceT.step e d ≠ (instDomainD.fn g).f μ₂ := by
  unfold Domain.fn instDomainD Trace.step instTraceT
  simp
  apply T.ne_ret_step ∘ Eq.symm

@[simp]
theorem D.ne_step_stuck : instTraceT.step e d ≠ instDomainD.stuck.f μ₂ := by
  unfold Domain.stuck instDomainD Trace.step instTraceT
  simp
  apply T.ne_ret_step ∘ Eq.symm

abbrev is_allocator (f : Heap → Addr) := ∀ μ, f μ ∉ μ

def nextFree (μ : Heap) : Addr := match μ.keys.maximum? with
| .none => 0
| .some n => n+1

theorem nextFree_is_allocator : is_allocator nextFree := by
  intro μ
  rw[AList.mem_keys]
  unfold nextFree
  split
  · simp_all
  · next n h =>
    unfold Addr at *
    have h := (List.maximum?_le_iff (by simp) h n).mp Nat.le.refl
    intro (habsurd : n+1 ∈ μ.keys)
    have h : n+1 ≤ n := h (n+1) habsurd
    omega

def fetch (a : Nat) : ▹ D :=
  next[f ← Later.unsafeFlip fun (μ : Heap) =>
    if _ : a ∈ μ
    then next[d ← μ[a]]. d.f μ
    else next[]. pure ⟨μ, Value.stuck⟩]. D.mk f

@[simp]
theorem fetch.eq1 (h : a ∈ μ) : (next[d ← fetch a]. d.f μ) = (next[d ← μ[a]]. d.f μ) := by
  unfold fetch; simp; rw[Later.unsafeFlip_eq]; simp[h]
@[simp]
theorem fetch.eq2 (h : a ∉ μ) : (next[d ← fetch a]. d.f μ) = (next[]. instDomainD.stuck.f μ) := by
  unfold fetch Domain.stuck instDomainD; simp; rw[Later.unsafeFlip_eq]; simp[h]

def stepLookFetch (x : Name) (a : Nat) : D :=
  D.mk fun μ =>
    if _ : a ∈ μ
    then Trace.step (Event.look x) (next[d ← μ[a]]. d.f μ)
    else Trace.step (Event.look x) (next[]. pure ⟨μ, Value.stuck⟩)

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

def get : ByNeed Heap := ByNeed.mk fun μ => T.ret ⟨μ,μ⟩
def put (μ : Heap) : ByNeed Unit := ByNeed.mk fun _ => T.ret ⟨μ,⟨⟩⟩

instance instHasBindD : HasBind D Later where
  bind _x rhs body := cast D.eq.symm do
    let μ ← get
    let a := nextFree μ
    put (μ[a ↦ memo a (next[]. rhs (fetch a))])
    body (fetch a)

instance : Applicative Later where
  pure a := Later.next (fun () => a)
  seq f a := Later.ap f (a ())

def evalByNeed : Exp → FinMap Name (EnvD D) → D := eval

def takeT (n : Nat) (t : T α) : (T.F α)^[n] Unit := match n, cast T.unfold t with
| 0, _ => ()
| .succ _, .ret a => cast (Function.iterate_succ_apply' _ _ _).symm (T.F.ret a)
| .succ n, .step e lt => cast (Function.iterate_succ_apply' _ _ _).symm (T.F.step e (takeT n (Later.unsafeForce lt)))

instance : Repr (Value.F p n) where
  reprPrec v _ := match v with
  | .stuck => "stuck"
  | .fun _ => "fun"

instance : Repr Heap where
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

-- #synth Repr ((T.F (Heap × Value))^[100] Unit)
-- #eval takeT 100 ((evalByNeed {} [exp| let id := fun x => x; id id |]).f {})
