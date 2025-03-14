import SEq

axiom MyVector : Nat → Type
axiom VectorA : {n : Nat} → MyVector n → Type
axiom VectorB : {n : Nat} → {v : MyVector n} → VectorA v → Type
axiom VectorC : {n : Nat} → {v : MyVector n} → {a : VectorA v} → VectorB a → Type

axiom mkVec : (n : Nat) → MyVector n
axiom mkVecA : {n : Nat} → (v : MyVector n) → VectorA v
axiom mkVecB : {n : Nat} → {v : MyVector n} → (a : VectorA v) → VectorB a
axiom mkVecC : {n : Nat} → {v : MyVector n} → {a : VectorA v} → (b : VectorB a) → VectorC b

/-- info: ⟨1, mkVec 1⟩ = ⟨1, mkVec 1⟩ : Prop -/
#guard_msgs in
#check mkVec 1 =[MyVector]= mkVec 1

/-- info: ⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩ = ⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩ : Prop -/
#guard_msgs in
#check mkVecA (mkVec 1) =[@VectorA]= mkVecA (mkVec 1)

/-- info: ⟨⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩, mkVecB (mkVecA (mkVec 1))⟩ =
  ⟨⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩, mkVecB (mkVecA (mkVec 1))⟩ : Prop -/
#guard_msgs in
#check mkVecB (mkVecA (mkVec 1)) =[@VectorB]= mkVecB (mkVecA (mkVec 1))

/-- info: ⟨⟨⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩, mkVecB (mkVecA (mkVec 1))⟩, mkVecC (mkVecB (mkVecA (mkVec 1)))⟩ =
  ⟨⟨⟨⟨1, mkVec 1⟩, mkVecA (mkVec 1)⟩, mkVecB (mkVecA (mkVec 1))⟩, mkVecC (mkVecB (mkVecA (mkVec 1)))⟩ : Prop -/
#guard_msgs in
#check mkVecC (mkVecB (mkVecA (mkVec 1))) =[@VectorC]= mkVecC (mkVecB (mkVecA (mkVec 1)))
