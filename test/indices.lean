import SEq

axiom Vector : Nat → Type
axiom VectorA : {n : Nat} → Vector n → Type
axiom VectorB : {n : Nat} → {v : Vector n} → VectorA v → Type
axiom VectorC : {n : Nat} → {v : Vector n} → {a : VectorA v} → VectorB a → Type

axiom mkVec : (n : Nat) → Vector n
axiom mkVecA : {n : Nat} → (v : Vector n) → VectorA v
axiom mkVecB : {n : Nat} → {v : Vector n} → (a : VectorA v) → VectorB a
axiom mkVecC : {n : Nat} → {v : Vector n} → {a : VectorA v} → (b : VectorB a) → VectorC b

/-- info: ⟨1, mkVec 1⟩ = ⟨1, mkVec 1⟩ : Prop -/
#guard_msgs in
#check mkVec 1 =[Vector]= mkVec 1

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
