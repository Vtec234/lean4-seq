import test.vector

-- This lemma interferes with `SEq` rewriting.
attribute [-simp] Sigma.mk.injEq

/-! ## Multiply indexed type families

In order to state equalities in type families with multiple indices,
we provide custom elaborators for `=[_]=` and `d[-]▸`
which compute the correct motive in terms of iterated dependent pairs. -/

inductive VectorH : {n : Nat} → MyVector Type n → Type 1
  | vnil : VectorH ⟦⟧
  | vcons {α : Type} {n : Nat} {v : MyVector Type n} :
    α → VectorH v → VectorH (α ::: v)

namespace VectorH

def vapp {n m} {u : MyVector Type n} {v : MyVector Type m} :
    VectorH u → VectorH v → VectorH (u +++ v)
  | vnil,      V => V
  | vcons a U, V => vcons a (vapp U V)

/-! ## VectorH cast calculus -/

@[pull_dcast]
theorem vcons_dcast {α : Type} {n m : Nat} {u : MyVector Type n} {v : MyVector Type m}
    (a : α) (V : VectorH u) (h : u =[MyVector Type]= v) :
    vcons a (h d[@VectorH]▸ V) = (MyVector.vcons_scongr α h) d[@VectorH]▸ (vcons a V) := by
  cases h
  simp

/-! ## Properties of VectorH operations -/

theorem vapp_vnil {n} {v : MyVector Type n} {V : VectorH v} : vapp vnil V =[@VectorH]= V := by
  induction V with
  | vnil => rfl
  | vcons a V ih =>
    simp [seq_iff_dcast_eq, vapp, eq_dcast_of_seq ih, eq_dcast_of_seq (MyVector.vapp_vnil _),
      MyVector.vapp]

theorem vapp_assoc {n m k} {u : MyVector Type n} {v : MyVector Type m} {w : MyVector Type k}
    (U : VectorH u) (V : VectorH v) (W : VectorH w) :
    vapp (vapp U V) W =[@VectorH]= vapp U (vapp V W) := by
  induction U with
  | vnil => rfl
  | vcons a U ih =>
    simp [pull_dcast, seq_iff_dcast_eq, vapp, eq_dcast_of_seq ih, MyVector.vapp,
      eq_dcast_of_seq (MyVector.vapp_assoc ..), Nat.add_assoc]

end VectorH

/-! ## hpattern -/

-- TODO: `generalize` could take a list of occurrences to abstract
