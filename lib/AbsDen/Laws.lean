import AbsDen.Semantics
import AbsDen.ByNeed
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints

namespace AbsDen

open IGDTT

instance [CompleteLattice A] : CompleteLattice (@Subtype A p) := sorry

abbrev idd := fun (x : Type) => x
instance : Applicative idd where
  pure := fun x => x
  seq := fun f a => f (a ())

class AbstractByNeedDomain (D : Type)
  extends CompleteLattice D,
          Domain D idd,
          HasBind D idd where
  monotonicity : True -- TODO
  step_app : Trace.step ev (Domain.ap d a) ≤ (Domain.ap (Trace.step ev d) a : D)
  stuck_app : Domain.stuck ≤ (Domain.ap d a : D)
  beta_app : f a ≤ (Domain.ap (Domain.fn f) a : D)
  by_name_bind : rhs d ≤ d → body d ≤ (HasBind.bind x rhs body : D)
  step_inc : d ≤ (Trace.step e d : D)
  step_upd : Trace.step Event.upd d = (d : D)



def GaloisConnection.repr_l [CompleteLattice B] (β : A → B) (S : Set A) : B :=
  sSup { β a | a : S }

def GaloisConnection.repr_u [CompleteLattice B] (β : A → B) (b : B) : Set A :=
  { a : A | β a ≤ b }

def GaloisConnection.repr [CompleteLattice B] (β : A → B) : GaloisConnection (repr_l β) (repr_u β) := by
  intros as b
  apply Iff.intro <;> (unfold repr_l repr_u; simp; intro h; exact h)

def PrefT α := Σ n, (T.F α)^[n] Unit  -- prefixes of T (Heap × Value)

mutual
noncomputable abbrev αD [AbstractByNeedDomain A] (μ : Heap) : Set D → A := GaloisConnection.repr_l (βD μ)
termination_by 0
decreasing_by sorry
noncomputable abbrev γD [AbstractByNeedDomain A] (μ : Heap) : A → Set D := GaloisConnection.repr_u (βD μ)
termination_by 0
decreasing_by sorry
noncomputable def βD [AbstractByNeedDomain A] (μ : Heap) (d : D) : A :=
  βT (d.f μ)
termination_by 0
decreasing_by sorry

noncomputable abbrev αEnvD [AbstractByNeedDomain A] (μ : Heap) (Ds : Set (EnvD D)) : EnvD A :=
  ⟨αD μ { d.1 | d : Ds }, sorry⟩

noncomputable abbrev γEnvD [AbstractByNeedDomain A] (μ : Heap) (a : EnvD A) : Set (EnvD D) :=
  { ⟨d, sorry⟩ | d : γD μ a.1 }
termination_by 0
decreasing_by sorry

noncomputable abbrev αT [AbstractByNeedDomain A] : Set (T (Heap × Value)) → A := GaloisConnection.repr_l βT
noncomputable abbrev γT [AbstractByNeedDomain A] : A → Set (T (Heap × Value)) := GaloisConnection.repr_u βT
noncomputable def βT [AbstractByNeedDomain A] (τ : T (Heap × Value)) : A :=
  ⨆ i, (βT_pref ⟨i, takeT i τ⟩)
termination_by 0
decreasing_by sorry

noncomputable def βT_pref [AbstractByNeedDomain A] : PrefT (Heap × Value) → A
| ⟨0, ()⟩ => ⊥
| ⟨n+1, τ⟩ => match cast (Function.iterate_succ_apply' _ _ _) τ with
| .step e τ => Trace.step e (βT_pref ⟨n, τ⟩)
| .ret ⟨μ, .stuck⟩ => Domain.stuck
| .ret ⟨μ, .fun f⟩ => Domain.fn (fun a => αD μ { f (EnvD.name e) (EnvD.tl e) | e : (γEnvD μ a) })
termination_by τ => τ.1
end

noncomputable def βE [AbstractByNeedDomain A] : (Heap × FinMap Name (EnvD D)) → FinMap Name (EnvD A) :=
  fun ⟨μ, ρ⟩ => ρ.map (αEnvD μ ∘ singleton)
noncomputable def αE [AbstractByNeedDomain A] : Set (Heap × FinMap Name (EnvD D)) → FinMap Name (EnvD A) := GaloisConnection.repr_l βE
noncomputable def γE [AbstractByNeedDomain A] : FinMap Name (EnvD A) → Set (Heap × FinMap Name (EnvD D)) := GaloisConnection.repr_u βE

noncomputable def αS (A : Type) [AbstractByNeedDomain A] (S : FinMap Name (EnvD D) → D) : FinMap Name (EnvD A) → A :=
  fun ρ => αT { (S μρ.1.2).f μρ.1.1 | μρ : (γE ρ) }


open Domain Trace Event in
noncomputable example [AbstractByNeedDomain A] :
    αS A (evalByNeed [exp| let id := (fun x y => y) id; id |]) {}
  = step let1 (step (look "id") (step app1 (step app2 (fn sorry))))
  := sorry

-- Definable entities

abbrev kern_r (f : α → β) : α → α → Prop := fun a b => f a = f b
namespace kern_r
private theorem refl {f : α → β} (a : α) : kern_r f a a := Eq.refl (f a)
private theorem symm {f : α → β} {a b : α} : kern_r f a b → kern_r f b a := Eq.symm
private theorem trans {f : α → β} {a b c : α} : kern_r f a b → kern_r f b c → kern_r f a c := Eq.trans
theorem is_eqv (f : α → β) : Equivalence (kern_r f) := ⟨kern_r.refl, kern_r.symm, kern_r.trans⟩
end kern_r

def kernSetoid (f : α → β) : Setoid α where
  r := kern_r f
  iseqv := kern_r.is_eqv f

structure DefiEnv.Repr where
  ρ : FinMap Name (EnvD D)
  property : ∀ x (h : x ∈ ρ), ∃a, EnvD.tl ρ[x] = fetch a

instance : Setoid DefiEnv.Repr := kernSetoid DefiEnv.Repr.ρ
def DefiEnv := Quotient (kernSetoid DefiEnv.Repr.ρ) -- I think the Quotient here is actually unnecessary; the equivalence is just defeq
namespace DefiEnv
def ρ : DefiEnv → FinMap Name (EnvD D) := Quotient.lift Repr.ρ (fun _ _ h => h)
private theorem Repr.erase_preserves {m : FinMap Name v} (h : k ∈ AList.erase k' m) :
    (m.erase k')[k] = let h2 := (AList.mem_erase.mp h).2; m[k] := by
  unfold GetElem.getElem instFinMapGetElem
  have h : AList.lookup k (AList.erase k' m) = AList.lookup k m := AList.lookup_erase_ne (AList.mem_erase.mp h).1
  -- cases h -- dependent elimination failed :(
  simp
  split
  split
  simp_all
private def Repr.erase (ρ : DefiEnv.Repr) (x : Name) : DefiEnv.Repr := ⟨ρ.ρ.erase x, fun y h => Repr.erase_preserves h ▸ ρ.property y (AList.mem_erase.mp h).2⟩
def erase : DefiEnv → Name → DefiEnv := Quotient.lift (fun ρ x => Quotient.mk' (Repr.erase ρ x)) fun a b h => by
  ext x; unfold Repr.erase; have : a.ρ.erase x = b.ρ.erase x := by {rw[h]}; simp only[this]
private def Repr.adom (ρ : DefiEnv.Repr) : Set Addr := { a | ∃x, (_ : x ∈ ρ.ρ) → EnvD.tl ρ.ρ[x] = fetch a}
def adom : DefiEnv → Set Addr := Quotient.lift Repr.adom (fun a b h => by unfold Repr.adom; rw[h])
end DefiEnv

structure DefiD.Repr where
  mk ::
  e : Exp
  ρ : DefiEnv
private abbrev DefiD.Repr.d (d : DefiD.Repr) := evalByNeed d.e d.ρ.ρ
instance : Setoid DefiD.Repr := kernSetoid DefiD.Repr.d
def DefiD := Quotient (kernSetoid DefiD.Repr.d)

namespace DefiD
def d : DefiD →  D := Quotient.lift DefiD.Repr.d (fun _ _ h => h)
private def garbage_free (d : DefiD.Repr) : Prop := ¬(∃ x, d.d = (Repr.mk d.e (d.ρ.erase x)).d)
private theorem gc_unique (d : DefiD.Repr) : ∃! ρ, garbage_free (Repr.mk d.e ρ) := sorry
private noncomputable def Repr.gc (d : DefiD.Repr) : DefiD.Repr := ⟨d.e, Classical.choose (gc_unique d)⟩
private theorem Repr.gc_sound {d : DefiD.Repr} : Repr.d d = Repr.d (Repr.gc d) := sorry
private noncomputable def gc : DefiD → DefiD := Quotient.lift (Quotient.mk' ∘ Repr.gc) sorry
private theorem gc_sound {d : DefiD} : d = gc d := by
  obtain ⟨r,h⟩ := Quotient.exists_rep d
  rw[←h]
  exact Quotient.sound Repr.gc_sound
private def Repr.adom (d : DefiD.Repr) : Set Addr := DefiEnv.adom (gc d).ρ
def adom : DefiD → Set Addr := Quotient.lift DefiD.Repr.adom fun a b h => by
  have hblah : Repr.d (Repr.gc a) = Repr.d (Repr.gc b) := (Repr.gc_sound (d := a).symm.trans h).trans (Repr.gc_sound (d:=b))
  have : gc ⟦a⟧ = gc ⟦b⟧ := have : ⟦a⟧ = ⟦b⟧ := Quotient.eq.mpr h; by congr;
  have : ⟦Repr.gc a⟧ = (⟦Repr.gc b⟧ : DefiD) := this;
  unfold Repr.adom Repr.ρ Repr.gc DefiEnv.adom DefiEnv.Repr.adom
  obtain ⟨ra,ha⟩ := Quotient.exists_rep (Classical.choose (gc_unique a))
  obtain ⟨hafree, hauni⟩ := Classical.choose_spec (gc_unique a)
  obtain ⟨rb,hb⟩ := Quotient.exists_rep (Classical.choose (gc_unique b))
  obtain ⟨hbfree, hbuni⟩ := Classical.choose_spec (gc_unique b)
  rw[←ha, ←hb] at *
  simp_all
  ext addr
  let prop (r : DefiEnv.Repr) : Prop := ∃ x, ∀ (_ : x ∈ r.ρ), EnvD.tl r.ρ[x] = fetch addr
  have hgoal (ra rb : DefiEnv.Repr) : prop ra → prop rb := sorry -- quite finicky and a bit beside the point for the work I want to do
  exact Iff.intro (hgoal ra rb) (hgoal rb ra)
def Repr.is_value (d : DefiD.Repr) : Prop := d.e.is_value
def is_value : DefiD → Prop := Quotient.lift DefiD.Repr.is_value sorry -- A boring proof utilising that Domain.fn is not Trace.step
end DefiD

abbrev DefiV := { d : DefiD // d.is_value }

instance : Coe DefiD D where coe := DefiD.d

abbrev DefiHeap.Repr := FinMap Addr DefiD
namespace DefiHeap.Repr
private def μ (μ : DefiHeap.Repr) : Heap := FinMap.map_with_key (fun a d => memo a (next[]. d.d)) μ
private def dom (μ : DefiHeap.Repr) : Set Addr := fun a => a ∈ μ
end DefiHeap.Repr
instance : Setoid DefiHeap.Repr := kernSetoid DefiHeap.Repr.μ
abbrev DefiHeap := Quotient (kernSetoid DefiHeap.Repr.μ)
namespace DefiHeap
def μ : DefiHeap → Heap := Quotient.lift DefiHeap.Repr.μ (fun _ _ h => h)
def dom : DefiHeap → Set Addr := Quotient.lift DefiHeap.Repr.dom fun a b h => by
  ext x
  have : x ∈ a.μ ↔ x ∈ b.μ := by rw[h]
  have : x ∈ a ↔ x ∈ b := by rw[FinMap.dom_map_with_key (m:=a), FinMap.dom_map_with_key (m:=b)]; exact this
  exact this
def replace : Addr → DefiD → DefiHeap → DefiHeap  := sorry
end DefiHeap

instance instDefiHeapMembership : Membership Addr DefiHeap := ⟨fun μ a => a ∈ μ.μ⟩
instance instDefiHeapGetElem : GetElem DefiHeap Addr (▹ D) Membership.mem where
  getElem μ a h := μ.μ[a]
notation:max f "[" k "↦" v "]" => AList.replace k v f

def Trace.steps (ev : List Event) (t : T (Heap × Value)) : T (Heap × Value) :=
  List.foldr (fun e t => Trace.step e (next[]. t)) t ev
@[simp]
lemma Trace.steps_nil : Trace.steps [] d = d := by unfold Trace.steps; simp
@[simp]
lemma Trace.steps_cons : Trace.steps (e::ev) d = Trace.step e (next[]. Trace.steps ev d) := by unfold Trace.steps; simp

structure BalancedExec (d₁ : DefiD) (μ₁ : DefiHeap) (d₂ : DefiD) (μ₂ : DefiHeap) where
  mk ::
  events : List Event
  is_value : d₂.is_value
  property : d₁.d.f μ₁.μ = Trace.steps events (d₂.d.f μ₂.μ)

structure StuckExec (d₁ : DefiD) (μ₁ : DefiHeap) where
  mk ::
  events : List Event
  μ₂ : DefiHeap
  property : d₁.d.f μ₁.μ = Trace.steps events (instDomainD.stuck.f μ₂.μ)

def Triple (P : DefiHeap → Prop) (d : DefiD) (Q : DefiV → DefiHeap → Prop) : Prop :=
  ∀ μ₁ events μ₂ v, P μ₁ → d.d.f μ₁.μ = Trace.steps events (v.val.d.f μ₂.μ) → Q v μ₂

notation:max "<" e₁:max "," μ₁:max ">⇓<" e₂:max "," μ₂:max ">" => BalancedExec e₁ μ₁ e₂ μ₂

lemma eval_deterministic : <d₁,μ₁>⇓<d₂,μ₂> → <d₁,μ₁>⇓<d₃,μ₃> → d₂ = d₃ ∧ μ₂ = μ₃ :=
  sorry

lemma ne_steps_fun_stuck :
  ∀ ev₁ ev₂ μ₁ μ₂ g, Trace.steps ev₁ ((instDomainD.fn g).f μ₁) ≠ Trace.steps ev₂ (instDomainD.stuck.f μ₂)
:= by
  intro ev₁ ev₂ _ _ _
  induction ev₁ generalizing ev₂
  case nil =>
    cases ev₂
    case nil => exact D.ne_stuck_fn ∘ Eq.symm
    case cons => unfold instDomainD Domain.fn; simp; exact T.ne_ret_step
  case cons _ ev₁' hind =>
    cases ev₂
    case nil => unfold instDomainD Domain.fn; simp; exact (T.ne_ret_step ∘ Eq.symm)
    case cons _ ev₂' =>
      simp;
      intro _ h;
      have h := Later.unsafeForce.eq ▸ Later.unsafeForce.eq ▸ congrArg Later.unsafeForce h
      apply hind ev₂' h

lemma balanaced_not_stuck (hbal : <⟨e,ρ₁⟩,μ₁>⇓<⟨v,ρ₂⟩,μ₂>) (hstuck : StuckExec ⟨e,ρ₁⟩ μ₁) : False := by
  have ⟨bal_events, ⟨x,e',hval⟩, bal_property⟩ := hbal
  simp at hval
  rw[hval] at bal_property
  have ⟨stuck_events, μ₃, stuck_property⟩ := hstuck
  have h := bal_property.symm.trans stuck_property
  apply ne_steps_fun_stuck
  assumption

inductive HeapProgression : DefiHeap → DefiHeap → Prop where
| refl : ---------------------
         HeapProgression μ₁ μ₁
| trans (h1 : HeapProgression μ₁ μ₂) (h2 : HeapProgression μ₂ μ₃) :
        ---------------------------------------------------------
                  HeapProgression μ₁ μ₃
| ext   {μ : DefiHeap} {a : Addr} {d : DefiD} (hfresh : a ∉ μ) (hgood : d.adom ⊆ μ.dom ∪ {a}) :
        --------------------------------------------------------------------------------------
                         HeapProgression μ μ[a↦d]
| memo  {μ₁ μ₂ : DefiHeap} {a : Addr} {e v : Exp} {ρ₁ ρ₂ : DefiEnv}
              (hdom : a ∈ μ₁) (hbefore : μ₁[a] = ⟨e, ρ₁⟩)
              (hevals : ▹ <⟨e,ρ₁⟩,μ₁>⇓<⟨v,ρ₂⟩,μ₂>) :
        -----------------------------------------------------------
                         HeapProgression μ₁ μ₂[a↦⟨v,ρ₂⟩]

notation μ₁ " ↝ " μ₂ => HeapProgression μ₁ μ₂

theorem funny : Triple (· = μ₁) d (fun v μ₂ => μ₁ ↝ μ₂) := sorry

lemma eval_progesses_heap : <⟨e,ρ₁⟩,μ₁>⇓<⟨v,ρ₂⟩,μ₂> → μ₁ ↝ μ₂ := gfix fun hind hevals => by
  have ⟨events, ⟨z,e',hval⟩, property⟩ := hevals
  simp at hval
  rw[hval] at property
  unfold DefiD.d evalByNeed eval at property
  simp at property
  cases e
  case var x =>
    simp at property
    split at property
    next hinscope =>
      obtain ⟨a,hfetch⟩ := ρ₁.property x hinscope
      generalize ρ₁.val[x] = entry at *
      simp at property
      cases events;
      · simp at property
      · simp at property; rw[hfetch] at property; unfold fetch at property; simp at property; rw[Later.unsafeFlip_eq] at property; split at property;  sorry
    next => absurd property.symm; apply ne_steps_fun_stuck events ([])
  case lam x e' =>
    simp at property
    cases events
    case cons => absurd property; exact D.ne_step_fn.symm
    case nil => simp at property; have := D.confuse_fn_heap property;
    sorry

lemma abs_ByNeed_interpretation' [AbstractByNeedDomain A] : αS A (evalByNeed e ρ) μ ≤ eval e := sorry
theorem abs_ByNeed_interpretation [AbstractByNeedDomain A] : αS A (evalByNeed e) ≤ eval e := sorry
