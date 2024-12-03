/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import SEq.Lemmas

open Lean Elab Meta

private theorem collapseDCastDCastRefl_aux
    {α α' : Type u} {β : α → Type v} {β' : α' → Type v} {a b : α} {a' b' : α'}
    (h : a = b) (h' : a' = b') (x : β a)
    (defEq₁ : β b = β' a') (defEq₂ : β' b' = β a) :
    defEq₂ ▸ h' d[β']▸ (defEq₁ ▸ (h d[β]▸ x) : β' a') = x := by
  cases h
  cases h'
  dsimp only [dcast_rfl]
  generalize β a = γ at x defEq₁ defEq₂
  cases defEq₁
  simp

/-- Simplification procedure that removes chained `dcast`s
in case the combined path is just `refl`. -/
-- TODO: what does [seval] attribute do?
simproc collapseDCastDCastRefl (dcast _ _ (dcast _ _ _)) := fun e'' => do
  let_expr dcast α' a' b' β' h' e' ← e'' | return .continue
  let_expr dcast α a b β h e ← e' | return .continue
  -- TODO: can this unintentionally assign something?
  if !(← isDefEq (mkApp β a) (mkApp β' b')) then
    return .continue
  let pf ← mkAppOptM ``collapseDCastDCastRefl_aux
    #[α, α', β, β', a, b, a', b', h, h', e, ← mkEqRefl (mkApp β b), ← mkEqRefl (mkApp β a)]
  return .done { expr := e, proof? := pf }

private theorem collapseEqRecEqRec_aux
    {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort w} (x : motive a rfl) {b : α} (h : a = b)
    {α' : Sort v} {a' : α'} {motive' : (b' : α') → a' = b' → Sort w} {b' : α'} (h' : a' = b')
    (defEq : motive b h = motive' a' rfl) :
    @Eq.rec α' a' motive'
      (@Eq.rec (Sort w) (motive b h) (fun x _ => x)
        (@Eq.rec α a motive x b h)
        (motive' a' rfl) defEq)
      b' h' =
    @Eq.rec (Sort w) (motive a rfl) (fun x _ => x) x (motive' b' h') (by simp [h, h', defEq]) := by
  cases h; cases h'; simp

/-- Simplification procedure that combines chained `Eq.rec` operations. -/
-- TODO: this has the downside of erasing motives
-- and replacing them with generic `fun x _ => x`, i.e., a `cast`.
simproc collapseEqRecEqRec (@Eq.rec _ _ _ (@Eq.rec _ _ _ _ _ _) _ _) := fun e'' => do
  let_expr Eq.rec α' a' motive' e' b' h' ← e'' | return .continue
  let_expr Eq.rec α a motive e b h ← e' | return .continue
  let rflA' ← mkEqRefl a'
  -- TODO: can this unintentionally assign something?
  if !(← isDefEq (mkApp2 motive b h) (mkApp2 motive' a' rflA')) then
    return .continue
  let pf ← mkAppOptM ``collapseEqRecEqRec_aux
    #[α, a, motive, e, b, h, α', a', motive', b', h', ← mkEqRefl (mkApp2 motive b h)]
  let_expr Eq _ _ newE ← (← inferType pf) | return .continue
  return .done { expr := newE, proof? := pf }
