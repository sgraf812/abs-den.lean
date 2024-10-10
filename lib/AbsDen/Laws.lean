import AbsDen.Semantics
import AbsDen.ByNeed
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints

namespace AbsDen

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

abbrev DefiEnv := { ρ : FinMap Name (EnvD D) // ∀ x (h : x ∈ ρ), ∃a, EnvD.tl ρ[x] = fetch a }
def DefiEnv.adom (ρ : DefiEnv) : Set Addr := { a | ∃x, (_ : x ∈ ρ.1) → EnvD.tl ρ.1[x] = fetch a}

structure DefiD where
  e : Exp
  ρ : DefiEnv
abbrev DefiD.d (d : DefiD) : D := evalByNeed d.e d.ρ
abbrev DefiD.adom (d : DefiD) : Set Addr := DefiEnv.adom d.ρ
instance : Coe DefiD D where coe := DefiD.d

abbrev DefiHeap := FinMap Addr DefiD
abbrev DefiHeap.μ (μ : DefiHeap) : Heap := FinMap.map_with_key (fun a d => memo a (next[]. d.d)) μ
abbrev DefiHeap.dom (μ : DefiHeap) : Set Addr := fun a => a ∈ μ.keys

structure EvaluatesTo (d₁ : DefiD) (μ₁ : DefiHeap) (d₂ : DefiD) (μ₂ : DefiHeap) where
  mk ::
  events : List Event
  is_value : d₂.e.is_value
  property : d₁.d.f μ₁.μ = List.foldr (fun ev τ => T.step ev (next[]. τ)) (d₂.d.f μ₂.μ) events

notation:max "<" e₁:max "," μ₁:max ">⇓<" e₂:max "," μ₂:max ">" => EvaluatesTo e₁ μ₁ e₂ μ₂

lemma eval_deterministic : <⟨e,ρ₁⟩,μ₁>⇓<⟨e₂,ρ₂⟩,μ₂> → <⟨e₁,ρ₁⟩,μ₁>⇓<⟨e₃,ρ₃⟩,μ₃> → e₂ = e₃ ∧ ρ₂ = ρ₃ ∧ μ₂ = μ₃ :=
  sorry

lemma eval_not_stuck : <⟨e,ρ₁⟩,μ₁>⇓<⟨v,ρ₂⟩,μ₂> →

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

open IGDTT

lemma eval_progesses_heap : <⟨e,ρ₁⟩,μ₁>⇓<⟨v,ρ₂⟩,μ₂> → μ₁ ↝ μ₂ := gfix fun hind hevals => by
  have ⟨events, is_value, property⟩ := hevals
  unfold DefiD.d evalByNeed eval at *
  simp at *
  cases e
  case var x => simp at property; split at property; cases events; simp at *;

lemma abs_ByNeed_interpretation' [AbstractByNeedDomain A] : αS A (evalByNeed e ρ) μ ≤ eval e := sorry
theorem abs_ByNeed_interpretation [AbstractByNeedDomain A] : αS A (evalByNeed e) ≤ eval e := sorry
