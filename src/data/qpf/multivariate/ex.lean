
inductive fin' : ℕ → Type
| raise {n : ℕ} : fin' n → fin' n.succ
| last {n : ℕ} : fin' n.succ

def fin'.elim0 {α} : fin' 0 → α .

universes u

def typevec (n : ℕ) := fin' n → Type*

def arrow {n} (α β : typevec n) := Π i : fin' n, α i → β i

infixl ` ⟹ `:40 := arrow
open nat

def append1 {n} (α : typevec n) (β : Type*) : typevec (n+1)
| (fin'.raise i) := α i
| fin'.last      := β

def repeat : Π (n : ℕ) (t : Sort*), typevec n
| 0 t := fin'.elim0
| (nat.succ i) t := append1 (repeat i t) t

-- def of_repeat : Π {n i} (x : repeat n Prop i), Prop
-- | (nat.succ n) (fin'.raise i) x := @of_repeat n i x
-- | (nat.succ n) fin'.last x := x

def of_repeat {n i} : repeat n Prop i → Prop :=
begin
  induction i with n i IH,
  { exact IH },
  { exact id }
end

namespace typevec

def id {n} {α : typevec n} : α ⟹ α := λ i x, x

def drop {n} (α : typevec (n+1)) : typevec n := λ i, α i.raise

def last {n} (α : typevec (n+1)) : Type* := α fin'.last

end typevec

open typevec

def drop_fun {n} {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.raise

infixl ` ::: `:67 := append1

-- def subtype_ : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), typevec n
-- | 0 := λ α p, fin'.elim0
-- | (succ n) := λ α p, @subtype_ n (drop α) (drop_fun p) ::: _root_.subtype (λ x, p fin'.last x)

def subtype_ {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop) : typevec n :=
λ i, begin
  induction i with n i IH generalizing α p,
  { exact @IH (drop α) (drop_fun p) },
  { exact _root_.subtype (λ x, p fin'.last x) }
end

def to_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), (λ (i : fin' n), { x // of_repeat $ p i x }) ⟹ subtype_ p
| (succ n) α p (fin'.raise i) x := to_subtype (drop_fun p) i x
| (succ n) α p fin'.last x := x

def of_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop),
  subtype_ p ⟹ (λ (i : fin' n), { x // of_repeat $ p i x })
-- := by intros n α p i; induction i; [apply i_ih, {intro x; exact x}]
| (succ n) α p (fin'.raise i) x := of_subtype _ i x
| (succ n) α p fin'.last x := x

example {i_n : ℕ}
  (i_a : fin' i_n)
  {α : typevec i_n.succ}
  (p : α ⟹ repeat i_n.succ Prop)
  (x : subtype_ p i_a.raise) :
  to_subtype p i_a.raise (of_subtype p i_a.raise x) = id i_a.raise x :=
begin
  rw [of_subtype,to_subtype],
  -- to_subtype p i_a.raise (of_subtype (drop_fun p) i_a x) = id i_a.raise x
  -- dsimp [of_subtype,to_subtype],
  -- to_subtype p i_a.raise (of_subtype (drop_fun p) i_a x) = id i_a.raise x
  admit
end

variables {m : ℕ} (i : fin' m) {α : typevec m.succ} (p : α ⟹ repeat m.succ Prop)
#check (rfl : subtype_ p i.raise = subtype_ (drop_fun p) i) -- works
#check λ (x : subtype_ p i.raise), show subtype_ (drop_fun p) i, from x -- fails
