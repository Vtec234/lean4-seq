import SEq.Tactic.DepRewrite

/-! Basic tests for `rewrite!`. -/

/-- Turn a term into a sort for testing. -/
axiom P.{u} {α : Sort u} : α → Prop

open Lean Elab Term in
/-- Produce the annotation ``.mdata .. e`` for testing.
Standard elaborators may represent projections as ordinary functions instead. -/
elab "mdata% " e:term : term => do
  let e ← elabTerm e none
  return .mdata ({ : MData}.insert `abc "def") e

open Lean Elab Meta Term in
/-- Produce the projection ``.proj `Prod 0 e`` for testing.
Standard elaborators may represent projections as ordinary functions instead. -/
elab "fst% " e:term : term => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (some <| .sort u)
  let β ← mkFreshExprMVar (some <| .sort v)
  let tp := mkApp2 (.const ``Prod [u, v]) α β
  let e ← elabTerm e tp
  return .proj ``Prod 0 e

/-! Tests for proof-only mode. -/

variable {n m : Nat} (eq : n = m)

-- mdata
example (f : (k : Nat) → 0 < k → Type) (lt : 0 < n) : P (mdata% f n lt) := by
  rewrite! [eq]
  guard_target = P (f m _)
  sorry

-- app (fn)
/-- error: function expected
  any x -/
#guard_msgs in
example (any : (α : Type) → α) (eq : (Nat → Nat) = Bool) :
    P (any (Nat → Nat) 0) := by
  rewrite! [eq]
  sorry

-- app (arg)
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) : P (f n ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target = P (f m ⟨0, _⟩)
  sorry

-- proj
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) :
    P (fst% ((⟨0, lt⟩, ()) : Fin n × Unit)) := by
  rewrite! [eq]
  guard_target = P (fst% ((⟨0, _⟩, ()) : Fin m × Unit))
  sorry

/-- error: projection type mismatch
  (any x).1 -/
#guard_msgs in
example (any : (α : Type) → α) (eq : (Nat × Nat) = Nat) :
    P (fst% any (Nat × Nat)) := by
  rw! [eq]
  sorry

-- let (value)
example (lt : 0 < n) :
    let A : Type := Fin n
    P (@id A ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =
    let A : Type := Fin m
    P (@id A ⟨0, _⟩)
  sorry

-- let (type)
example (lt : 0 < n) :
    let x : Fin n := ⟨0, lt⟩
    P (@id (Fin n) x) := by
  rewrite! [eq]
  guard_target =
    let x : Fin m := ⟨0, _⟩
    P (@id (Fin m) x)
  sorry

-- let (proof)
example (lt' : 0 < n) : P (let lt : 0 < n := lt'; @Fin.mk n 0 (@id (0 < n) lt)) := by
  rewrite! [eq]
  guard_target = P (let lt : 0 < m := eq ▸ lt'; @Fin.mk m 0 (@id (0 < m) _))
  sorry

-- lam
example : P fun (y : Fin n) => y := by
  rewrite! [eq]
  guard_target = P fun (y : Fin m) => y
  sorry

-- lam (proof)
example : P fun (lt : 0 < n) => @Fin.mk n 0 (@id (0 < n) lt) := by
  rewrite! [eq]
  guard_target = P fun (lt : 0 < m) => @Fin.mk m 0 (@id (0 < m) _)
  sorry

/-- error: cannot cast
  y
to expected type
  Fin n
in cast mode 'proofs' -/
#guard_msgs in
example (Q : Fin n → Prop) (q : (x : Fin n) → Q x) :
    P fun y : Fin n => q y := by
  rewrite! [eq]
  sorry

/-! Tests for all-casts mode. -/

variable (B : Nat → Type)

-- app (polymorphic fn)
example (f : (k : Nat) → B k → Nat) (b : B n) : P (f n b) := by
  rewrite! (castMode := .all) [eq]
  guard_target = P (f m (eq ▸ b))
  sorry

-- app (monomorphic fn)
example (f : B n → Nat) (b : (k : Nat) → B k) : P (f (b n)) := by
  rewrite! (castMode := .all) [eq]
  guard_target = P (f (eq ▸ b m))
  sorry

-- lam
example (f : B n → Nat) : P fun y : B n => f y := by
  rewrite! (castMode := .all) [eq]
  guard_target = P fun y : B m => f (eq ▸ y)
  sorry

/-- error: tactic 'drewrite' failed, did not find instance of the pattern in the target expression
  n
n m : Nat
eq : n = m
B : Nat → Type
f : B n → Nat
b : B n
⊢ f b = f b -/
#guard_msgs in
example (f : B n → Nat) (b : B n) :
    f b = f b := by
  rewrite! [eq]
  sorry
