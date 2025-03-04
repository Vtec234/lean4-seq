/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Wojciech Nawrocki
-/
import Lean.Elab.Tactic

namespace SEq.Tactic.DRewrite
open Lean Meta

theorem dcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : (a' : α) → @Eq α a a' → Sort v} (h : @Eq α a a')
    (f : (a' : α) → (h : @Eq α a a') → β a' h) :
    f a (@Eq.refl α a) =
    @Eq.rec α a' (fun x h' ↦ β x (@Eq.trans α a a' x h h')) (f a' h) a (@Eq.symm α a a' h) :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

theorem nddcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : Sort v} (h : @Eq α a a') (f : (a' : α) → (h : @Eq α a a') → β) :
    f a (@Eq.refl α a) = f a' h :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

theorem heqL.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq α a (@cast β α (@Eq.symm (Sort u) α β (@type_eq_of_heq α β a b h)) b) :=
  HEq.rec (Eq.refl a) h

theorem heqR.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq β (@cast α β (@type_eq_of_heq α β a b h) a) b :=
  HEq.rec (Eq.refl a) h

initialize
  registerTraceClass `drewrite
  registerTraceClass `drewrite.visit
  registerTraceClass `drewrite.cast

/-- Determines which, if any, type-incorrect subterms
should be casted along the equality that `drewrite` is rewriting by. -/
inductive CastMode where
  /-- Don't insert any casts. -/
  | none
  /-- Only insert casts on proofs.

  In this mode, it is *not* permitted to cast subterms of proofs that are not themselves proofs.
  For example, given `y : Fin n`, `P : Fin n → Prop`, `p : (x : Fin n) → P x` and `eq : n = m`,
  we will not rewrite `p y : P y` to `p (eq ▸ y) : P (eq ▸ y)`. -/
  | proofs
  -- TODO: `proofs` plus "good" user-defined casts such as `Fin.cast`.
  -- | userDef
  /-- Insert as many `Eq.rec`s as necessary. -/
  | all
deriving BEq

instance : ToString CastMode := ⟨fun
  | .none => "none"
  | .proofs => "proofs"
  | .all => "all"⟩

def CastMode.toNat : CastMode → Nat
  | .none => 0
  | .proofs => 1
  | .all => 2

instance : LE CastMode where
  le a b := a.toNat ≤ b.toNat

instance : DecidableLE CastMode :=
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

structure Config where
  transparency : TransparencyMode := .reducible
  offsetCnstrs : Bool := true
  occs : Occurrences := .all
  castMode : CastMode := .proofs

structure Context where
  cfg : DRewrite.Config
  /-- The pattern to generalize over. -/
  p : Expr
  /-- The free variable to substitute for `p`. -/
  x : Expr
  /-- A proof of `p = x`. Must be an fvar. -/
  h : Expr
  pHeadIdx : HeadIndex := p.toHeadIndex
  pNumArgs : Nat := p.headNumArgs
  subst : FVarSubst := {}

/-- Monad for computing `dabstract`.
The cache is for `visit` (not `visitAndCast`, which has two arguments),
and the `Nat` tracks which occurrence of the pattern we are currently seeing. -/
abbrev M := ReaderT Context <| MonadCacheT ExprStructEq Expr <| StateRefT Nat MetaM

/-- Check that casting `e : t` to `et` is allowed in the current mode. -/
def checkCastAllowed (e t et : Expr) : M Unit := do
  let ctx ← read
  let throwMismatch : Unit → M Unit := fun _ => do
    throwError "cannot cast{indentD e}\nto expected type{indentD et}\nin cast mode '{ctx.cfg.castMode}'"
  if ctx.cfg.castMode == .none then
    throwMismatch ()
  if ctx.cfg.castMode == .proofs && !(← isProp t) then
    throwMismatch ()

/-- If `e : te` is a term whose type mentions `x` or `h` (the generalization variables),
return `⋯ ▸ e : te[p/x,rfl/h]`.
Otherwise return `none`. -/
def castBack? (e te : Expr) : M (Option Expr) := do
  let ctx ← read
  if !te.hasFVar || !te.hasAnyFVar (fun f => f == ctx.x.fvarId! || f == ctx.h.fvarId!) then
    return none
  let motive ←
    withLocalDeclD `x' (← inferType ctx.x) fun x' => do
    withLocalDeclD `h' (← mkEq ctx.x x') fun h' => do
      mkLambdaFVars #[x', h'] <| te.replaceFVars #[ctx.x, ctx.h] #[x', ← mkEqTrans ctx.h h']
  some <$> mkEqRec motive e (← mkEqSymm ctx.h)

def withSubst? (x tx : Expr) (k : M α) : M α := do
  match ← castBack? x tx with
  | some e =>
    -- We do NOT check whether this is an allowed cast here
    -- because it might not ever be used
    -- (e.g. if the bound variable is never mentioned).
    withReader (fun ctx => { ctx with subst := ctx.subst.insert x.fvarId! e }) k
  | none => k

mutual

/-- Given `e`, return `e[x/p]` (i.e., `e` with occurrences of `p` replaced by `x`).
If `et?` is not `none`, the output is guaranteed to have type (defeq to) `et?`.

Does _not_ assume that `e` is well-typed,
but assumes that for all subterms `e'` of `e`,
`e'[x/p]` is well-typed.
We use this when processing lambdas:
to traverse `fun (x : α) => b`,
we add `x : α[x/p]` to the local context
and continue traversing `b`.
`x : α[x/p] ⊢ b` may be ill-typed,
but the output `x : α[x/p] ⊢ b[x/p]` is well-typed. -/
partial def visitAndCast (e : Expr) (et? : Option Expr) : M Expr := do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
  if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te' et then
    return e'
  trace[drewrite.cast] "casting{indentD e'}\nto expected type{indentD et}"
  checkCastAllowed e' te' et
  -- Try casting from the inferred type,
  -- and if that doesn't work,
  -- casting to the expected type.
  let ctx ← read
  if let some e'' ← castBack? e' te' then
    let te'' ← inferType e''
    if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te'' et then
      trace[drewrite.cast] "from inferred type (x ↦ p):{indentD e'}"
      return e''
  let motive ← mkLambdaFVars #[ctx.x, ctx.h] et
  let e' ← mkEqRec motive e' ctx.h
  trace[drewrite.cast] "to expected type (p ↦ x):{indentD e'}"
  return e'

/-- Like `visitAndCast`, but does not insert casts at the top level.
The expected types of certain subterms are computed from `et?`. -/
partial def visit (e : Expr) (et? : Option Expr) : M Expr :=
  withTraceNode `drewrite.visit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => 💥️") do
  checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if ← isProof e then
    /- Recall that `e` might be type-incorrect.
    We assume it will become type-correct after traversal,
    but by proof irrelevance we can skip traversing proofs,
    instead casting them at the top-level.
    However, in this case we need to fix `e`
    by applying the delayed substitution `subst`
    which replaces bound variables with type-correct terms.
    We do not do this eagerly when introducing binders
    because it can introduce more casts than necessary. -/
    -- QUESTION(WN): in `.proofs` cast mode,
    -- can this observably 'leak' non-proof casts in the type of `ctx.subst.apply e`?
    return ctx.subst.apply e
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← getMCtx
    if ← isDefEq e ctx.p then
      let i ← modifyGet fun i => (i, i+1)
      if ctx.cfg.occs.contains i then
        return ctx.x
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
  match e with
  | .mdata _ b => return e.updateMData! (← visitAndCast b et?)
  | .app f a =>
    let fup ← visit f none
    let tfup ← inferType fup
    withAtLeastTransparency .default <| forallBoundedTelescope tfup (some 1) fun xs _ => do
      let #[r] := xs | throwFunctionExpected fup
      let tr ← inferType r
      let aup ← visitAndCast a tr
      return .app fup aup
  | .proj n i b =>
    let bup ← visit b none
    let tbup ← inferType bup
    if !tbup.isAppOf n then
      throwError m!"projection type mismatch{indentD <| Expr.proj n i bup}"
    return e.updateProj! bup
  | .letE n t v b _ =>
    let tup ← visit t none
    let vup ← visitAndCast v tup
    withLetDecl n tup vup fun l => do
    withSubst? l tup do
      let bup ← visitAndCast (b.instantiate1 l) et?
      return e.updateLet! tup vup (bup.abstract #[l])
  | .lam _ t b _ =>
    match et? with
    | some et =>
      forallBoundedTelescope et (some 1) fun xs bet => do
        let #[r] := xs | throwError m!"function type expected{indentD et}"
        withSubst? r (← inferType r) do
          let bup ← visitAndCast (b.instantiate1 r) bet
          mkLambdaFVars xs bup
    | none =>
      let tup ← visit t none
      lambdaBoundedTelescope (e.updateLambdaE! tup b) 1 fun xs b => do
        let #[r] := xs | throwError m!"internal error: lambda expected"
        withSubst? r tup do
          let bup ← visit b none
          mkLambdaFVars xs bup
  | .forallE _ t b _ =>
    let tup ← visit t none
    forallBoundedTelescope (e.updateForallE! tup b) (some 1) fun xs b => do
      let #[r] := xs | throwError m!"internal error: forall expected"
      withSubst? r tup do
        let bup ← visit b none
        mkForallFVars xs bup
  | _ => return e

end

def dabstract (e : Expr) (p : Expr) (cfg : DRewrite.Config) : MetaM Expr := do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode `drewrite (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> 💥️{indentD err.toMessageData}") do
  withLocalDeclD `x tp fun x => do
  withLocalDeclD `h (← mkEq p x) fun h => do
    let e' ← visit e none |>.run { cfg, p, x, h } |>.run |>.run' 1
    mkLambdaFVars #[x, h] e'

/--
Rewrite goal `mvarId` dependently.
-/
def _root_.Lean.MVarId.depRewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : DRewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `drewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `drewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `drewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <|
            dabstract e lhs config
          let nAbst ← withLocalDeclD .anonymous α fun a ↦ do withLocalDeclD .anonymous (← mkEq lhs a) fun h ↦ do
            mkLambdaFVars #[a, h] e
          if ← withReducible (withNewMCtxDepth <| isDefEq eAbst nAbst) then
            throwTacticEx `drewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          try
            check eAbst
          catch e : Lean.Exception =>
            throwTacticEx `drewrite mvarId <|
              m!"motive{indentD eAbst}\nis not type correct:{indentD e.toMessageData}\n" ++
              m!"unlike with rw/rewrite, this error should NOT happen in rw!/rewrite!:\n" ++
              m!"please report it on the Lean Zulip"
          -- construct rewrite proof
          let eType ← inferType e
          let eNew := match (← instantiateMVars eAbst) with
            | .lam _ _ b _ => b.instantiate1 rhs
            | _ => .app eAbst rhs
          let eNew := match (← instantiateMVars eNew) with
            | .lam _ _ b _ => b.instantiate1 heq
            | _ => .app eNew heq
          let (motive, dep) ← withLocalDeclD `_a α fun a ↦ do withLocalDeclD `_h (← mkEq lhs a) fun h ↦ do
            let motive ← inferType (.app (.app eAbst a) h)
            return (← mkLambdaFVars #[a, h] motive, not (← withNewMCtxDepth <| isDefEq motive eType))
          let u1 ← getLevel α
          let u2 ← getLevel eType
          -- `eqPrf : eAbst[lhs,rfl] = eNew`
          -- `eAbst[lhs,rfl] ≡ target`
          let (eNew, eqPrf) ← do
            if dep then
              let eNew ← withLocalDeclD `x α fun x ↦ do withLocalDeclD `h (← mkEq rhs x) fun h ↦ do
                let motive ← mkLambdaFVars #[x, h] (.app (.app motive x) (← mkEqTrans heq h))
                mkEqRec motive eNew (← mkEqSymm heq)
              pure (eNew, mkApp6 (.const ``dcongrArg [u1, u2]) α lhs rhs motive heq eAbst)
            else
              pure (eNew, mkApp6 (.const ``nddcongrArg [u1, u2]) α lhs rhs eType heq eAbst)
          postprocessAppMVars `drewrite mvarId newMVars binderInfos
            (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
          let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed heqIn
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq lhs rhs
        | true  => do
          cont (← mkEqSymm heq) rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst ``propext) lhs rhs heq
      cont heq heqType
    | none => match heqType.heq? with
      | some (α, lhs, β, rhs) =>
        let heq ← mkAppOptM (if symm then ``heqR else ``heqL) #[α, β, lhs, rhs, heq]
        cont heq (← inferType heq)
      | none =>
        cont heq heqType

/--
The configuration used by `rw!` to call `dsimp`.
This configuration uses only iota reduction (recursor application) to simplify terms.
-/
private def depRwContext : MetaM Simp.Context :=
  Simp.mkContext
    {Lean.Meta.Simp.neutralConfig with
     etaStruct := .none
     iota := true
     failIfUnchanged := false}

open Parser Elab Tactic

/--
`rewrite!` is like `rewrite`, but can also rewrite inside types by inserting casts.
This means that the 'motive is not type correct' error never occurs,
at the expense of potentially creating complicated terms.
It is also available as a `conv` tactic.

The sort of casts that are inserted is controlled by the `castMode` configuration option.
By default, only proof terms are casted:
by proof irrelevance, this adds no observable complexity. -/
syntax (name := depRewriteSeq) "rewrite!" optConfig rwRuleSeq (location)? : tactic

/--
`rw!` is like `rewrite!`, but also calls `dsimp` to simplify the result after every substitution.
It is also available as a `conv` tactic.
-/
syntax (name := depRwSeq) "rw!" optConfig rwRuleSeq (location)? : tactic

def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DRewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def depRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : DRewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

declare_config_elab elabDRewriteConfig Config

@[tactic depRewriteSeq] def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")

@[tactic depRwSeq] def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabDRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")
    -- copied from Lean.Elab.Tactic.evalDSimp
    dsimpLocation (← depRwContext) #[] loc

namespace Conv
open Conv

/-- `rewrite! [thm]` rewrites the target dependently using `thm`. See the `rewrite!` tactic for more information. -/
syntax (name := depRewrite) "rewrite!" (config)? rwRuleSeq (location)? : conv

/-- `rw! [thm]` rewrites the target using `thm`. See the `rw!` tactic for more information. -/
syntax (name := depRw) "rw!" (config)? rwRuleSeq (location)? : conv

def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DRewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwTarget (stx : Syntax) (symm : Bool) (config : DRewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    -- copied from Lean.Elab.Conv.Simp
    changeLhs (← dsimp (← getLhs) (← depRwContext)).1
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : DRewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  let dsimpResult := (← dsimp rwResult.eNew (← depRwContext)).1
  let replaceResult ← replaceResult.mvarId.changeLocalDecl replaceResult.fvarId dsimpResult
  replaceMainGoal (replaceResult :: rwResult.mvarIds)

@[tactic depRewrite]
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← DRewrite.elabDRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (DRewrite.depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")

@[tactic depRw]
def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← DRewrite.elabDRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")
    -- Note: in this version of the tactic, `dsimp` is done inside `withLocation`.
    -- This is done so that `dsimp` will not close the goal automatically.

end Conv
end SEq.Tactic.DRewrite
