import SEq

-- This lemma interferes with `SEq` rewriting.
attribute [-simp] Sigma.mk.injEq

/-! ## Test case: proofs about intrinsically sized vectors

From *HEq: a Coq library for Heterogeneous Equality*
(https://sf.snu.ac.kr/publications/heq.pdf).

Note: no constructor or function is forded here;
we carry proofs of index equality in `dcast` and `=[_]=` instead. -/

inductive MyVector : Type u → Nat → Type u
  | vnil (α) : MyVector α 0
  | vcons {α} {n} : α → MyVector α n → MyVector α (n + 1)
  deriving Repr, BEq

namespace MyVector

def vapp {α n m} : MyVector α n → MyVector α m → MyVector α (m + n)
  | vnil _,    v => v
  | vcons a u, v => vcons a (vapp u v)

notation "⟦⟧" => MyVector.vnil _
infixr:67 " ::: " => MyVector.vcons
infixl:65 " +++ " => MyVector.vapp

def vrev {α n} : MyVector α n → MyVector α n
  | vnil _      => vnil _
  | vcons hd tl => (by omega) d[MyVector α]▸ (vrev tl +++ hd ::: ⟦⟧)

/-! ## "Indexed cast calculus" for MyVector operations

`pull_dcast` rules pull casts outwards. -/

@[pull_dcast]
theorem vcons_dcast {α : Type u} {n m : Nat} (a : α) (v : MyVector α n) (h : n = m) :
    a ::: h d[MyVector α]▸ v = (h ▸ rfl) d[MyVector α]▸ (a ::: v) := by
  cases h
  simp

@[pull_dcast]
theorem vapp_dcast_left {α : Type u} {n m k : Nat}
      (u : MyVector α n) (h : n = m) (v : MyVector α k) :
    h d[MyVector α]▸ u +++ v = (h ▸ rfl) d[MyVector α]▸ (u +++ v) := by
  cases h
  simp

@[pull_dcast]
theorem vapp_dcast_right {α : Type u} {n m k : Nat}
      (u : MyVector α n) (v : MyVector α m) (h : m = k)  :
    u +++ h d[MyVector α]▸ v = (h ▸ rfl) d[MyVector α]▸ (u +++ v) := by
  cases h
  simp

/-! ## Congruence laws -/

-- NOTE: These helper lemmas may be superseded by a `srw` tactic/term elaborator. -/

theorem vcons_scongr {α : Type u} {n m : Nat} {u : MyVector α n} {v : MyVector α m} (a : α)
    (h : u =[MyVector α]= v) : a ::: u =[MyVector α]= a ::: v := by
  simp [pull_dcast, seq_iff_dcast_eq, eq_dcast_of_seq h, idx_eq_of_seq h]

/-! ## Properties of MyVector operations -/

theorem vapp_vnil {α n} (v : MyVector α n) : v +++ ⟦⟧ =[MyVector α]= v := by
  induction v with
  | vnil => rfl
  | vcons a v ih =>
    rename_i n
    simp [pull_dcast, vapp, seq_iff_dcast_eq, eq_dcast_of_seq ih]

theorem vapp_assoc {α n m k} (u : MyVector α n) (v : MyVector α m) (w : MyVector α k) :
    (u +++ v) +++ w =[MyVector α]= u +++ (v +++ w) := by
  induction u with
  | vnil => rfl
  | vcons a w ih => simp [pull_dcast, seq_iff_dcast_eq, eq_dcast_of_seq ih, vapp, Nat.add_assoc]

theorem vrev_vapp {α n m} (u : MyVector α n) (v : MyVector α m) :
    vrev (u +++ v) =[MyVector α]= vrev v +++ vrev u := by
  induction u with
  | vnil => simp [seq_iff_dcast_eq, eq_dcast_of_seq (vapp_vnil _), vapp, vrev]
  | vcons a u ih =>
    simp [pull_dcast, vrev, vapp,
      seq_iff_dcast_eq, eq_dcast_of_seq ih, eq_dcast_of_seq (vapp_assoc ..),
      Nat.add_comm]

/-! ## Final boss: tail-recursive rev -/

def vrev_tailRec {α n} (v : MyVector α n) : MyVector α n :=
  (by omega) d[MyVector α]▸ go ⟦⟧ v
where go {n m : Nat} (acc : MyVector α n) : MyVector α m → MyVector α (n + m)
  | vnil _      => acc
  -- TODO: does leanc see through the cast and compile this as tail-recursive?
  | vcons a v => (by omega) d[MyVector α]▸ go (a ::: acc) v

@[csimp]
theorem vrev_eq_vrev_tailRec : @vrev = @vrev_tailRec := by
  ext1 α
  suffices ∀ {n m} (u : MyVector α n) (v : MyVector α m), vrev_tailRec.go u v =[MyVector α]= vrev v +++ u by
    ext n v
    simp [vrev_tailRec, eq_dcast_of_seq (this ..), eq_dcast_of_seq (vapp_vnil _)]
  intro n m u v
  induction v generalizing n u with
  | vnil => rfl
  | vcons a v ih =>
    simp [pull_dcast, seq_iff_dcast_eq, vrev_tailRec.go, eq_dcast_of_seq (ih _), vrev, eq_dcast_of_seq (vapp_assoc ..), vapp]

/-! Not a bad proof at all!
Key point is that `eq_dcast_of_seq` allows rewriting by `SEq`,
and `pull_dcast` lemmas normalize the resulting `dcast`s
until we end up with `dcast h a = dcast h' a`
which is true by proof-irrelevance. -/

/-! ## Actually that wasn't the final boss: pushing casts

Sometimes we need to *push* `dcast` downwards.
We use a `push_dcast` simpset for this. -/

def vplus {n} : MyVector Nat n → MyVector Nat n → MyVector Nat n
  | vnil _,    vnil _    => vnil _
  | vcons a u, vcons b v => (a + b) ::: vplus u v

@[push_dcast]
theorem push_vcons_dcast {α : Type u} {n m : Nat} (a : α) (v : MyVector α n) (h : n + 1 = m + 1) :
    h d[MyVector α]▸ (a ::: v) = a ::: (by simpa using h) d[MyVector α]▸ v := by
  simp [pull_dcast]

-- "Now we consider the following goal."
example {n m} (u : MyVector Nat n) (v : MyVector Nat m) (a b : Nat) :
    vplus (a ::: (u +++ v)) ((by omega) d[MyVector Nat]▸ (b ::: (v +++ u))) =[MyVector Nat]=
    (a + b) ::: vplus (u +++ v) ((by omega) d[MyVector Nat]▸ (v +++ u)) := by
  simp [push_dcast, vplus]

end MyVector
