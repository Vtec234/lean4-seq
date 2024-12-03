import SEq

variable {α α' : Type u} {β : α → Type v} {a b : α'} {f : α' → α}
    (h : a = b) (hf : f b = f a) (x : β (f a))

example : hf d[β]▸ (h d[fun a => β (f a)]▸ x) = x := by
  simp only [collapseDCastDCastRefl]

example : hf d[β]▸ (h d[fun a => β (f a)]▸ x) = x := by
  simp only [dcast, collapseEqRecEqRec]
