import AbsDen.Semantics
import Mathlib.Data.List.AList
import Mathlib.Algebra.Ring.Basic
import Mathlib.Order.Bounds.Basic

inductive U where | U0 | U1 | Uω deriving BEq
open U
abbrev botU := U0

def lubU : U → U → U
| .U0, u   => u
| u,   .U0 => u
| .U1, .U1 => .U1
| _,   _   => Uω

def addU : U → U → U
| .U0, u => u
| u, .U0 => u
| _, _   => Uω

def mulU : U → U → U
| .U0, _ => U0
| _, .U0 => U0
| .U1, u => u
| u, .U1 => u
| _, _   => Uω

instance : Add U where
  add := addU

instance : Mul U where
  mul := mulU


def eraseBotU (u : FinMap Name U) : FinMap Name U := Id.run do
  let mut res := u
  for ⟨k,v⟩ in u.entries do
    if v == U0 then res := res.erase k
  pure res

abbrev Uses := Quot (fun a b => eraseBotU a = eraseBotU b)
instance : DecidableEq Uses :=
  fun u1 u2 => by aesop?

instance : EmptyCollection Uses where
  emptyCollection := Quot.mk _ {}

def lubUses (l : Uses) (r : Uses) : Uses :=
  Quot.mk _ (Quot.lift (Quot.lift (FinMap.unionWith lubU) sorry l) sorry r)

instance : Add Uses where
  add l r :=
    Quot.mk _ (Quot.lift (Quot.lift (FinMap.unionWith addU) sorry l) sorry r)

instance : HMul U Uses Uses where
  hMul u1 u2 :=
    Quot.mk _ (Quot.lift (FinMap.map (mulU u1)) sorry u2)

structure UT (v : Type) :=
  mk ::
  uses : Uses
  val : v

-- #synth DecidableEq (Quot (fun (a : Int) (b: Int) => a = b))

instance [DecidableEq v] : DecidableEq (UT v) :=
  fun ⟨u1,v1⟩ ⟨u2,v2⟩ =>
    match decEq u1 with
    | isTrue e₁ =>
      match decEq b b' with
      | isTrue e₂  => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse n₂ => isFalse fun h => Prod.noConfusion h fun _   e₂' => absurd e₂' n₂
    | isFalse n₁ => isFalse fun h => Prod.noConfusion h fun e₁' _   => absurd e₁' n₁


def stepUT : Event → UT v → UT v
| .look x, ⟨φ, v⟩ => ⟨φ + Quot.mk _ (AList.singleton x U1), v⟩
| _,       t     => t
instance : Trace id (UT v) where
  step := stepUT

instance : Monad UT where
  pure v := ⟨Quot.mk _ {}, v⟩
  bind us k := match us with | ⟨φ,v⟩ => let ⟨φ2, v'⟩ := k v; ⟨φ+φ2, v'⟩

inductive UValue where
| rep : U → UValue
| cons : U → UValue → UValue

def peel : UValue → U × UValue
| .cons u v => ⟨u, v⟩
| .rep u    => ⟨u, UValue.rep u⟩

abbrev UD := UT UValue

instance : Domain UD (isEnv id UD) where
  stuck := ⟨{}, UValue.rep U0⟩
  fn x f := f ⟨Trace.step (L:=id) (Event.look x) ⟨{}, UValue.rep Uω⟩, ⟨_,_,rfl⟩⟩
  ap d a := match d, a with
    | ⟨φ,v⟩, ⟨⟨φ2,_⟩,_⟩ => let ⟨u,v'⟩ := peel v; ⟨φ + u*φ2, v'⟩



partial instance : HasBind id UD where
  bind _x rhs body :=
    let iter (old : UD) : UD :=
      let new := rhs old
      if old = new then old else iter new
    let d := iter ⟨{}, UValue.rep botU⟩
    body d
