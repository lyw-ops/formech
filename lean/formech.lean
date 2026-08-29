import Mathlib.Data.Vector.Basic

/- global variables -/
variable (n : ℕ)
abbrev B := ℕ
abbrev Pred (T : Type) := T → Bool

universe u

/- the notation of T ^ n -/
abbrev Ntuple (T : Type u) (n : ℕ) := Vector T n

instance : HPow (Type u) ℕ (Type u) where
  hPow := Ntuple

namespace Vector

/- without the nth element -/
def wtnth {T : Type} {n : ℕ} (t : T ^ n) (i : Fin n) : T ^ (n - 1) :=
  t.eraseIdx i

/- before the nth element -/
def lttnth {T : Type} {n : ℕ} (t : T ^ n) (i : Fin n) : T ^ i.val :=
  Vector.cast (Nat.min_eq_left i.isLt.le) (t.take i)

/- after the nth element -/
def gttnth {T : Type} {n : ℕ} (t : T ^ n) (i : Fin n) : T ^ (n - (i + 1)) :=
  t.drop (i + 1)

def tnth {T : Type} {n : ℕ} (t : T ^ n) (i : Fin n) : T := t.get i

end Vector

notation:max t "_{" i "}" => Vector.tnth t i
notation:max t "_{-" i "}" => Vector.wtnth t i
notation:max t "_{<" i "}" => Vector.lttnth t i
notation:max t "_{>" i "}" => Vector.gttnth t i

namespace Agent

abbrev type := Fin n

end Agent

notation:max "A#(" n ")" => Agent.type n

def Social_Welfare_Function {act : Type} {O : Type} := act ^ n → Pred O

local notation "SWF" => Social_Welfare_Function

def Tie_Break {O : Type} := Pred O → O

local notation "TB" => Tie_Break

namespace Mech

structure type {act : Type} (n : ℕ) where
 O : Type
 M : act ^ n -> O

instance {act : Type} {n : ℕ} :
    CoeFun (type (act := act) n) (fun mech => act ^ n → mech.O) where
  coe mech := mech.M

end Mech

namespace Mech_with_break

structure type {act : Type} (n : ℕ) where
  O : Type
  swf : @Social_Welfare_Function n act O
  tb : @Tie_Break O

def toMech {act : Type} {n : ℕ} (m : type (act := act) n) :
    Mech.type (act := act) n where
  O := m.O
  M := fun t ↦ m.tb (m.swf t)

end Mech_with_break

namespace Prefs

section Prefs

variable (act : Type)

local notation "M" => @Mech.type act n

local notation "Strategy" => A#(n) -> act

structure type (m : M) where
  V : Strategy /-"true value" strategy, mapping each agent private true
                       value, or "type", to an action/message-/
  U : A#(n) -> Mech.type.O m -> ℕ   /- utility -/
  T : Strategy /- strategy used in [m] -/

end Prefs

end Prefs

section DsIC

variable (act : Type)

variable (m : @Mech.type act n)

variable (p : Prefs.type n act m)

local notation "profile" => act ^ n

def differ_on (π π' : profile) (a : A#(n)) : Prop :=
  ∀ a', a' ≠ a → π' _{a'} = π _{a'}

def truthful' (π π' : profile) (a : A#(n)) : Prop :=
  differ_on n act π π' a → π _{a} = p.V a → p.U a (m π') ≤ p.U a (m π)

def truthful : Prop :=
  ∀ π π' (a : A#(n)), truthful' n act m p π π' a

end DsIC

namespace Single_Item_Auction

def Base (n : ℕ) : Bool → Type 1
  | true => Mech_with_break.type (act := B) n
  | false => Mech.type (act := B) n

def toMech : (br : Bool) → Base n br → Mech.type (act := B) n
  | true, m => Mech_with_break.toMech m
  | false, m => m

structure type (br : Bool) where
  base : Base n br
  p : (toMech n br base).O → Agent.type n → Option B

def type.M {n : ℕ} {br : Bool} (auction : type n br) :
    B ^ n → (toMech n br auction.base).O :=
  (toMech n br auction.base).M

instance {n : ℕ} {br : Bool} :
    CoeFun (type n br) (fun auction => B ^ n → (toMech n br auction.base).O) where
  coe auction := auction.M

variable {br : Bool} (auction : type n br) (v : Agent.type n → B)

def U (ai : A#(n)) (o : (toMech n br auction.base).O) : ℕ :=
  match auction.p o ai with
  | some p => v ai - p
  | none => 0

def prefs : Prefs.type (act := B) n (toMech n br auction.base) where
  V := v
  U := U n auction v
  T := v

end Single_Item_Auction