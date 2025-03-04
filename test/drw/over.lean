import SEq.Tactic.DepRewrite

/-! (MVP extracted from) rewriting in slice categories. -/

axiom C : Type
axiom Hom : C → C → Type
axiom comp {X Y Z : C} : Hom X Y → Hom Y Z → Hom X Z

structure Over (X : C) : Type where
  left : C
  hom : Hom left X

structure OverHom {X : C} (U V : Over X) : Type where
  left : Hom U.left V.left
  w : comp left V.hom = U.hom

def homMk {X : C} (U V : Over X) (f : Hom U.left V.left) (w : comp f V.hom = U.hom) : OverHom U V :=
  OverHom.mk f w

-- Destruct enough to turn terms that block `cases h` from proceeding into fvars
example (A X : C) (f : Over A) (x : (b : Hom X A) × (OverHom (Over.mk _ b) f)) :
    HEq (homMk (Over.mk _ (comp x.2.left f.hom)) f x.2.left rfl) x.2 := by
  obtain ⟨_, g, h⟩ := x
  dsimp at g h
  cases h
  rfl

-- Write motive by hand
example (A X : C) (f : Over A) (x : (b : Hom X A) × (OverHom (Over.mk _ b) f)) :
    HEq (homMk (Over.mk _ (comp x.2.left f.hom)) f x.2.left rfl) x.2 := by
  have h := x.2.w
  dsimp at h ⊢
  refine Eq.rec
    (motive := fun a h' =>
      @HEq
        (OverHom (Over.mk X a) f)
        (homMk (Over.mk X a) f x.2.left (h.trans h'))
        (OverHom (Over.mk X x.1) f)
        x.2)
    ?_
    h.symm
  rfl

-- Use `rw!`
example (A X : C) (f : Over A) (x : (b : Hom X A) × (OverHom (Over.mk _ b) f)) :
    HEq (homMk (Over.mk _ (comp x.2.left f.hom)) f x.2.left rfl) x.2 := by
  rewrite! [x.2.w]
  rfl
