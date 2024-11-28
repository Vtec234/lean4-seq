/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import SEq.Basic

variable {α : Type u} {a b c : α} {β : α → Type v} {x : β a} {y : β b}

@[simp]
theorem dcast_rfl (h : a = a) (x : β a) : h d[β]▸ x = x := by
  rfl

@[simp]
theorem dcast_dcast (h : a = b) (h' : b = c) (x : β a) :
    h' d[β]▸ (h d[β]▸ x) = (h.trans h') d[β]▸ x := by
  cases h
  simp

theorem seq_iff_dcast_eq : x =[β]= y ↔ ∃ (h : a = b), h d[β]▸ x = y := by
  constructor
  . intro h
    cases h
    simp
  . intro ⟨h, h'⟩
    cases h
    rw [dcast_rfl] at h'
    simp [h']

theorem seq_iff_eq_dcast : x =[β]= y ↔ ∃ (h : b = a), x = h d[β]▸ y := by
  constructor
  . intro h
    cases h
    simp
  . intro ⟨h, h'⟩
    cases h
    rw [dcast_rfl] at h'
    simp [h']

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
