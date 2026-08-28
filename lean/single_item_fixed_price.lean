import formech

local notation "B" => ℕ

namespace Single_Item_Fixed_Price

variable {n : ℕ} (posted_price : ℕ)

def le_p_bi (β : B ^ n) (i : Fin n) : Bool :=
  decide (posted_price <= β.get i)

def swf : @Social_Welfare_Function n B (Option A#(n)) :=
  fun β outcome =>
    match outcome with
    | some i => le_p_bi posted_price β i
    | none => (Fin.find? (le_p_bi (n := n) posted_price β)).isNone

/- acceptable : Option (Agent.type n) → Bool -/
def tb : @Tie_Break (Option (Agent.type n)) :=
  fun acceptable => Fin.find? fun i => acceptable (some i)

def payment (outcome : Option A#(n)) (a : A#(n)) : Option B :=
  match outcome with
  | some winner => if winner.val = a.val then some posted_price else none
  | none => none

def auction : Single_Item_Auction.type n true where
  base :=
    { O := Option (Agent.type n)
      swf := swf posted_price
      tb := tb}
  p := payment posted_price

section Example

/- an instance of fixed-price-auction -/
def fpa : Single_Item_Auction.type 3 true := auction (n := 3) 10

def bids1 : B ^ 3 := #v[7, 12, 12]

def m : Mech.type (act := B) 3 :=
  Single_Item_Auction.toMech 3 true fpa.base

def o1 : Option A#(3) := m.M bids1

#eval o1

#eval fpa.p o1 0
#eval fpa.p o1 1
#eval fpa.p o1 2

def bids2 : B ^ 3 := #v[3, 7, 9]

def o2 : Option A#(3) := m.M bids2

#eval o2

#eval fpa.p o2 0
#eval fpa.p o2 1
#eval fpa.p o2 2

end Example

end Single_Item_Fixed_Price
