import formech

-- local notation "B" => ℕ

namespace Single_Item_Fixed_Price

variable {n : ℕ} (posted_price : ℕ)

def lt_p_bi (β : B ^ n) (i : Fin n) : Bool :=
  decide (posted_price <= β _{i})

def swf : @Social_Welfare_Function n B (Option A#(n)) :=
  fun β outcome =>
    match outcome with
    | some i => lt_p_bi posted_price β i
    | none => false

/- acceptable : Option (Agent.type n) → Bool -/
def tb : @Tie_Break (Option A#(n)) :=
  fun acceptable => Fin.find? fun i => acceptable (some i)

def payment (outcome : Option A#(n)) (a : A#(n)) : Option B :=
  match outcome with
  | some winner => if winner.val = a.val then some posted_price else none
  | none => none

def auction : Single_Item_Auction.type n true where
  base :=
    { O := Option A#(n)
      swf := swf posted_price
      tb := tb}
  p := payment posted_price

section Truthful

variable (v : A#(n) → B)

def winner (β : B ^ n) : Option A#(n) :=
  Fin.find? fun i => decide (posted_price ≤ β _{i})

lemma auction_eq_winner (β : B ^ n) : auction posted_price β = winner posted_price β := rfl

lemma winner_ne {β : B ^ n} {a : A#(n)}
    (h : ∃ j, j < a ∧ posted_price ≤ β _{j}) : winner posted_price β ≠ some a := by
  rintro hwin
  rcases h with ⟨j, hja, hj⟩
  rw [winner] at hwin
  simpa [hj] using (Fin.find?_eq_some_iff.mp hwin).2 j hja

lemma winner_self {β : B ^ n} {a : A#(n)} (ha : posted_price ≤ β _{a})
    (h : ¬ ∃ j, j < a ∧ posted_price ≤ β _{j}) : winner posted_price β = some a :=
  Fin.find?_eq_some_iff.mpr ⟨by simpa using ha,
    fun j hja => by simp [show ¬ posted_price ≤ β _{j} from fun hj => h ⟨j, hja, hj⟩]⟩

lemma utility_eq (a : A#(n)) (o : Option A#(n)) :
    Single_Item_Auction.U n (auction posted_price) v a o =
      if o = some a then v a - posted_price else 0 := by
  cases o with
  | none => rfl
  | some winner =>
    simp only [Single_Item_Auction.U, auction, payment]
    by_cases h : winner = a
    · subst winner
      rw [if_pos rfl, if_pos rfl]
    · have hval : winner.val ≠ a.val := fun e => h (Fin.ext e)
      have hs : some winner ≠ some a := fun e => h (Option.some.inj e)
      rw [if_neg hval, if_neg hs]

theorem truthful :
    @_root_.truthful n B
      (Single_Item_Auction.toMech n true (auction posted_price).base)
      (Single_Item_Auction.prefs n (auction posted_price) v) := by
  intro π π' a hdifferent hself
  replace hself : π _{a} = v a := hself
  change Single_Item_Auction.U n (auction posted_price) v a (auction posted_price π') ≤
    Single_Item_Auction.U n (auction posted_price) v a (auction posted_price π)
  rw [auction_eq_winner posted_price π', auction_eq_winner posted_price π,
    utility_eq, utility_eq]
  by_cases hprice : posted_price ≤ v a
  · by_cases hblock : ∃ j, j < a ∧ posted_price ≤ π _{j}
    · rcases hblock with ⟨j, hja, hj⟩
      have hne : j ≠ a := by
        intro h
        subst j
        exact (Nat.lt_irrefl a.val hja)
      have hblock' : ∃ k, k < a ∧ posted_price ≤ π' _{k} :=
        ⟨j, hja, by
          calc
            posted_price ≤ π _{j} := hj
            _ = π' _{j} := (hdifferent j hne).symm⟩
      simp [winner_ne posted_price ⟨j, hja, hj⟩, winner_ne posted_price hblock']
    · have ha : posted_price ≤ π _{a} := by simpa [hself] using hprice
      have hπ : winner posted_price π = some a := winner_self posted_price ha hblock
      rw [if_pos hπ]
      split <;> simp
  · have hπ : winner posted_price π ≠ some a := by
      rintro hwin
      rw [winner] at hwin
      exact hprice (by simpa [hself] using Fin.eq_true_of_find?_eq_some hwin)
    have hz : v a - posted_price = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hprice))
    simp [hπ, hz]

end Truthful

section Example

/- an instance of fixed-price-auction -/

#check Single_Item_Fixed_Price.truthful (n := 3) 10

def fpa : Single_Item_Auction.type 3 true := auction 10

def bids1 : B ^ 3 := #v[7, 12, 12]

def o1 : Option A#(3) := fpa bids1

#eval o1

#eval fpa.p o1 0
#eval fpa.p o1 1
#eval fpa.p o1 2

def bids2 : B ^ 3 := #v[3, 7, 9]

def o2 : Option A#(3) := fpa bids2

#eval o2

#eval fpa.p o2 0
#eval fpa.p o2 1
#eval fpa.p o2 2

end Example

end Single_Item_Fixed_Price
