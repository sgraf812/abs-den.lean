import AbsDen.Semantics
import AbsDen.ByNeed
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints

namespace AbsDen

instance [CompleteLattice A] : CompleteLattice (@Subtype A p) := sorry

abbrev idd := fun (x : Type) => x

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

def PrefT α := Σ n, (T.F α)^[n] Unit  -- prefixes of T (Heap (▹ D) × Value)

mutual
noncomputable abbrev αD [AbstractByNeedDomain A] (μ : Heap (▹ D)) : Set D → A := GaloisConnection.repr_l (βD μ)
termination_by 0
decreasing_by sorry
noncomputable abbrev γD [AbstractByNeedDomain A] (μ : Heap (▹ D)) : A → Set D := GaloisConnection.repr_u (βD μ)
termination_by 0
decreasing_by sorry
noncomputable def βD [AbstractByNeedDomain A] (μ : Heap (▹ D)) (d : D) : A :=
  βT (d.f μ)
termination_by 0
decreasing_by sorry

noncomputable abbrev αEnvD [AbstractByNeedDomain A] (μ : Heap (▹ D)) (Ds : Set (EnvD D)) : EnvD A :=
  ⟨αD μ { d.1 | d : Ds }, sorry⟩
termination_by 0
decreasing_by sorry

noncomputable abbrev γEnvD [AbstractByNeedDomain A] (μ : Heap (▹ D)) (a : EnvD A) : Set (EnvD D) :=
  { ⟨d, sorry⟩ | d : γD μ a.1 }
termination_by 0
decreasing_by sorry

noncomputable abbrev αT [AbstractByNeedDomain A] : Set (T (Heap (▹ D) × Value)) → A := GaloisConnection.repr_l βT
termination_by 0
decreasing_by sorry
noncomputable abbrev γT [AbstractByNeedDomain A] : A → Set (T (Heap (▹ D) × Value)) := GaloisConnection.repr_u βT
termination_by 0
decreasing_by sorry

noncomputable def βT [AbstractByNeedDomain A] (τ : T (Heap (▹ D) × Value)) : A :=
  ⨆ i, (βT_pref ⟨i, takeT i τ⟩)
termination_by 0
decreasing_by sorry

noncomputable def βT_pref [AbstractByNeedDomain A] : PrefT (Heap (▹ D) × Value) → A
| ⟨0, ()⟩ => ⊥
| ⟨n+1, τ⟩ => match cast (Function.iterate_succ_apply' _ _ _) τ with
| .step e τ => Trace.step e (βT_pref ⟨n, τ⟩)
| .ret ⟨μ, .stuck⟩ => Domain.stuck
| .ret ⟨μ, .fun f⟩ => Domain.fn (fun a => αD μ { f (EnvD.name e) (EnvD.tl e) | e : (γEnvD μ a) })
termination_by τ => τ.1
end

noncomputable def βE [AbstractByNeedDomain A] : (Heap (▹ D) × FinMap Name (EnvD D)) → FinMap Name (EnvD A) :=
  fun ⟨μ, ρ⟩ => ρ.map (αEnvD μ ∘ singleton)
noncomputable def αE [AbstractByNeedDomain A] : Set (Heap (▹ D) × FinMap Name (EnvD D)) → FinMap Name (EnvD A) := GaloisConnection.repr_l βE
noncomputable def γE [AbstractByNeedDomain A] : FinMap Name (EnvD A) → Set (Heap (▹ D) × FinMap Name (EnvD D)) := GaloisConnection.repr_u βE

noncomputable def αS [AbstractByNeedDomain A] (eval : FinMap Name (EnvD D) → Exp → D) : FinMap Name (EnvD A) → Exp → A :=
  fun ρ e => αT { (eval μρ.1.2 e).f μρ.1.1 | μρ : (γE ρ) }


-- def α : [AbstractByNeedDomain A] → D → A :=
