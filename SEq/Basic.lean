/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Term
import Lean.Meta.Tactic.Simp.RegisterCommand

namespace SEq.LeftSigma
open Lean Meta Elab Term

/-!
The `dcast` motive for a dependent family with multiple indices
is parameterized by a *left-associated* dependent sum of the indices.
For example, `VectorS : (n : Nat) → (v : Vector n) → (h : VectorH n v) → Type`
gives rise to the motive
`fun (p : Σ (v : Σ (n : Nat), Vector n), VectorH v.1 v.2) ↦ VectorS p.1.1 p.1.2 p.2`.

Right-associated `Σ` is bad because an equality of these is, for example,
`n = m ∧ HEq (h : (v : Vector n) × VectorH n v) (h' : (v : Vector n) × VectorH m v)`
which does not entail `h.1 = h'.1`.
-/

/-- The (zero-indexed) `i`-th projection
from a left-associated dependent sum `e : Σ (…), …` with `n` components.
Assumes `i < n`. -/
def mkLeftSigmaProjection (e : Expr) (i n : Nat) : Expr :=
  (n - i).foldRev (init := e) fun j e =>
    if i == 0 && j == 0 then e
    else .proj ``Sigma (if j == 0 then 1 else 0) e

/-- Supposing `sigma = Σ (…), … : Type u` is a left-associated dependent sum
providing all the arguments of `A #(k-1) … #2 #1 #0 : Type v`,
return `Σ (p : sigma), A … p.1.1.2 p.1.2 p.2 : Type (max u v)`. -/
def mkLeftSigmaBVars (n : Name) (bi : BinderInfo) (u v : Level) (sigma A : Expr) (k : Nat) : Expr :=
  let sigPs := k.fold (init := #[]) fun i acc => acc.push <|
    mkLeftSigmaProjection (.bvar 0) i k
  let b := mkLambda n bi sigma (A.instantiateRev sigPs)
  mkApp2 (.const ``Sigma [u, v]) sigma b

/-- Supposing `b` is a term with free variables `xs : Array Expr`,
bind `xs` in `b` in a lambda `fun (p : Σ (…), …) ↦ b[pᵢ/xᵢ]`
where the binder type is a left-associated dependent sum of the types of `xs`
and `pᵢ` is the `i`-th projection from `p`. -/
def mkLeftSigmaLambda (n : Name) (bi : BinderInfo) (xs : Array Expr) (b : Expr) : MetaM Expr := do
  if 0 == xs.size then
    throwError "cannot compute dependent sum of no components"
  let (sigma, _) ← xs.size.foldM (init := (.bvar 1337, .zero)) fun i (s, u) => do
    match ← getFVarLocalDecl xs[i]! with
    | .cdecl _ _ n ty bi _ =>
      let .sort (.succ v) ← inferType ty
        | throwError "expected a type, got {ty}"
      if i == 0 then
        return (ty, v)
      let lvl := Level.normalize (.max u v)
      return (mkLeftSigmaBVars n bi u v s (ty.abstractRange i xs) i, lvl)
    | .ldecl .. => panic! "let-binding not supported"
  let sigPs := xs.size.fold (init := #[]) fun i acc => acc.push <|
    mkLeftSigmaProjection (.bvar 0) i xs.size
  return mkLambda n bi sigma ((b.abstract xs).instantiateRev sigPs)

def mkLeftSigma (xs : Array Expr) (A : Expr) : MetaM Expr := do
  if 0 == xs.size then
    return A
  let SA ← mkLeftSigmaLambda `p default xs A
  mkAppM ``Sigma #[SA]

/-- A left-associated dependent pair term `` `(⟨⟨…, _⟩, $e⟩) ``. -/
def mkLeftSigmaTerm (e : Term) : Nat → MetaM Term
  | 0 => return e
  | n+1 => do
    let h ← `(_)
    let s ← mkLeftSigmaTerm h n
    `(⟨$s, $e⟩)

/-- Notation for equality between elements of a type family
which elaborates to an equality of dependent pairs.
For families with implicit arguments, use `=[@β]=`.

When stating an equality of elements
whose types are propositionally but not definitionally equal,
it is common to use heterogeneous equality `HEq`.
However, when manipulating elements of a type family `β : α → Type`
with propositionally equal indices `a = b : α`,
it is better to use an equality of dependent pairs `@Eq (Sigma β) ⟨a, x⟩ ⟨b, y⟩` instead.
This is because `HEq x y` implies `β a = β b`, but not `a = b`
because type constructors are not provably injective
(in fact, injectivity of all type constructors is inconsistent with excluded middle:
https://lists.chalmers.se/pipermail/agda/2010/001522.html).
In contrast, an equality of dependent pairs directly entails `a = b`.
Indeed, `@Eq (Sigma β) ⟨a, x⟩ ⟨b, y⟩` is equivalent to `a = b ∧ HEq x y`. -/
-- Hypothesis: this is about as general as `HEq`,
-- as most (all?) nontrivial type equalities arise from index equality.
elab:50 a:term:51 " =[" β:term "]=" b:term:51 : term => do
  let β ← elabTerm β none
  let (n, Sigmaβ) ← forallTelescopeReducing (← inferType β) fun xs _ => do
    if xs.size == 0 then
      return (0, β)
    let Sigmaβ ← mkLeftSigma xs (mkAppN β xs)
    return (xs.size, Sigmaβ)
  -- NOTE: can write a custom elaborator for `⟨…, $a⟩` in case the syntactic approach fails.
  let a ← elabTerm (← mkLeftSigmaTerm a n) Sigmaβ
  let b ← elabTerm (← mkLeftSigmaTerm b n) Sigmaβ
  mkAppOptM ``Eq #[Sigmaβ, a, b]

end SEq.LeftSigma

/-- Like `cast` but stores a motive and a proof of index equality.
This is better than `cast` for building data:
see the docstring on `=[_]=` for motivation.

This is `tr` in agda-unimath, and `eq_rect` in Rocq. -/
@[macro_inline]
def dcast {α : Type u} {a b : α} (β : α → Type v) : a = b → β a → β b :=
  -- `ndrecOn` is an abbrev that simps to `Eq.rec`,
  -- but we do not want to simp `dcast` to `Eq.rec` (.. or do we?).
  Eq.ndrecOn

namespace SEq.DCast
open LeftSigma
open Lean Meta Elab Term

/-- Notation for `dcast` with an explicitly provided motive.
The term `h d[β]▸ t` elaborates to `dcast β' h t`,
where the motive `β'` is computed from `β`.
This is analogous to how `▸` produces `Eq.rec`,
except that `▸` behaves like the tactic `rw` and infers the motive. -/
syntax:75 term:75 "d[" term:75 "]▸" term:75 : term

initialize registerTraceClass `dcast

elab_rules : term
  | `($h d[ $β ]▸ $t) => do
    let β ← elabTerm β none
    let motive ← forallTelescopeReducing (← inferType β) fun xs _ => do
      if xs.size == 0 then
        return β
      mkLeftSigmaLambda `p default xs (mkAppN β xs)
    trace[dcast] m!"motive = {motive}"

    let u ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort u)
    let a ← mkFreshExprMVar α
    -- Bizarre: skipping this `check` makes the next step fail sometimes
    check (mkApp motive a)
    let t ← elabTerm t (mkApp motive a)
    let b ← mkFreshExprMVar α
    let h ← elabTerm h (mkApp3 (mkConst ``Eq [u]) α a b)

    mkAppOptM `dcast #[α, a, b, motive, h, t]

end SEq.DCast

namespace SEq.Tactic

/-- The simpset `push_dcast` stores lemmas which push `dcast` into subexpressions.
For example, `dcast β _ (a :: b) = a :: dcast β _ b`. -/
register_simp_attr push_dcast

/-- The simpset `pull_dcast` stores lemmas which pull `dcast` out of subexpressions.
For example, `a :: dcast β _ b = dcast β _ (a :: b)`. -/
register_simp_attr pull_dcast

end SEq.Tactic
