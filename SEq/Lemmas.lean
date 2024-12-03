/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import SEq.Basic

variable {α : Type u} {a b c : α} {β : α → Type v} {x : β a} {y : β b}

/-! ## `dcast` lemmas -/

@[simp]
theorem dcast_rfl (h : a = a) (x : β a) : h d[β]▸ x = x := by
  rfl

@[simp]
theorem dcast_dcast (h : a = b) (h' : b = c) (x : β a) :
    h' d[β]▸ (h d[β]▸ x) = (h.trans h') d[β]▸ x := by
  cases h
  simp

theorem dcast_comp {α' : Type u} {a b : α'} {f : α' → α} (h : a = b) (x : β (f a)) :
    h d[fun x => β (f x)]▸ x = (congrArg f h) d[β]▸ x := by
  cases h
  simp

theorem Sigma.eq_iff_dcast_eq {p q : Sigma β} :
    p = q ↔ ∃ (h : p.fst = q.fst), h d[β]▸ p.snd = q.snd := by
  constructor
  . intro h
    cases h
    simp
  . intro ⟨h, h'⟩
    let ⟨_, _⟩ := p
    let ⟨_, _⟩ := q
    cases h
    cases h'
    rfl

theorem Sigma.eq_iff_eq_dcast {p q : Sigma β} :
    p = q ↔ ∃ (h : p.fst = q.fst), p.snd = h.symm d[β]▸ q.snd := by
  constructor
  . intro h
    cases h
    simp
  . intro ⟨h, h'⟩
    let ⟨_, _⟩ := p
    let ⟨_, _⟩ := q
    cases h
    cases h'
    rfl

/-! ## `SEq` lemmas -/

theorem seq_iff_dcast_eq : x =[β]= y ↔ ∃ (h : a = b), h d[β]▸ x = y :=
  Sigma.eq_iff_dcast_eq

theorem seq_iff_eq_dcast : x =[β]= y ↔ ∃ (h : a = b), x = h.symm d[β]▸ y :=
  Sigma.eq_iff_eq_dcast

theorem seq_iff_eq_and_heq : x =[β]= y ↔ a = b ∧ HEq x y := by
  constructor
  . intro h
    cases h
    exact ⟨rfl, .refl _⟩
  . intro ⟨ab, xy⟩
    cases ab
    cases xy
    rfl

theorem idx_eq_of_seq (h : x =[β]= y) : a = b :=
  (seq_iff_dcast_eq.mp h).1

theorem dcast_eq_of_seq  (h : x =[β]= y) : (idx_eq_of_seq h) d[β]▸ x = y :=
  (seq_iff_dcast_eq.mp h).2

theorem eq_dcast_of_seq  (h : x =[β]= y) : x = (idx_eq_of_seq h).symm d[β]▸ y :=
  (seq_iff_eq_dcast.mp h).2
