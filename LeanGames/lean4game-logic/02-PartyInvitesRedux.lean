
-- Level 3 / 8 : Practise Makes Perfect
example (P Q R S : Prop)(h'₁ : P)(h'₂ : Q)(h'₃ : R)(h'₄ : S) : (P ∧ Q) ∧ R ∧ S := by
  constructor
  · constructor
    · assumption
    · assumption
  · constructor
    · assumption
    · assumption


-- Level 5 / 8 : Rinse and Repeat
example (P Q : Prop)(h: P ∧ Q) : Q := by
  cases h
  -- Q (Anton): Why does it work? Is it cause the local context has "unnamed" `right✝`?
  -- So assumption does not only go through my initial assumptions, but all assumptions
  -- in the local context?
  assumption


example (P Q : Prop)(h: P ∧ Q) : Q := by
  cases h with
  | intro left right => exact right


example (P Q : Prop)(h: P ∧ Q) : Q := by
  obtain ⟨p, q⟩ := h
  exact q


-- Level 6 / 8 : Nothing New
example (P Q R S : Prop)(h1 : P ∧ Q)(h2 : R ∧ S) : P ∧ S := by
  cases h1
  cases h2
  constructor
  · assumption
  · assumption


example (P Q R S : Prop)(h1 : P ∧ Q)(h2 : R ∧ S) : P ∧ S := by
  cases h1 with
  | intro p q =>  -- Q (Anton): Is there a way to introduce p, q, but avoid => and indentation? See next example.
    cases h2 with
    | intro r s =>
      apply And.intro
      · exact p
      · exact s


example (P Q R S : Prop)(h1 : P ∧ Q)(h2 : R ∧ S) : P ∧ S := by
  cases h1 with
  | intro p q  -- Q (Anton): How do I introduce p, q and continue without =>
  cases h2 with
  | intro r s
  apply And.intro
  · exact p
  · exact s


example (P Q R S : Prop)(h1 : P ∧ Q)(h2 : R ∧ S) : P ∧ S := by
  obtain ⟨p, q⟩ := h1
  obtain ⟨r, s⟩ := h2
  constructor
  · assumption
  · assumption


-- Level 7 / 8 : More Cases
-- The following solution works in the game, but seems to not work here
example (P Q : Prop)(h: (Q ∧ (((Q ∧ P) ∧ Q) ∧ Q ∧ Q ∧ Q)) ∧ (Q ∧ Q) ∧ Q) : P := by
  cases h
  cases left
  cases right_1
  cases left
  cases left_2
  assumption


example (P Q : Prop)(h: (Q ∧ (((Q ∧ P) ∧ Q) ∧ Q ∧ Q ∧ Q)) ∧ (Q ∧ Q) ∧ Q) : P := by
  -- Q (Anton): The `constructor` operates on the goal and can desctructure it figuring out the type
  -- of the goal for me. Is there something similar for destructuring assumptions? It seems that for
  -- `obtain`, I need to manually reconstruct the structure of the assumption, while in case of the
  -- `constructor` it is taken care of for me.
  obtain ⟨⟨_, ⟨⟨⟨_, p⟩ , _⟩, _⟩⟩ , _⟩ := h
  exact p


example (P Q : Prop)(h: (Q ∧ (((Q ∧ P) ∧ Q) ∧ Q ∧ Q ∧ Q)) ∧ (Q ∧ Q) ∧ Q) : P := by
  rcases h with ⟨⟨_, ⟨⟨⟨_, p⟩ , _⟩, _⟩⟩ , _⟩
  assumption


-- Level 8 / 8 : And Tactic Boss
-- The following solution works in the game, but seems to not work here
example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  cases h
  cases left
  cases left_1
  cases right
  cases right_3
  cases left_2
  constructor
  assumption
  constructor
  assumption
  constructor
  assumption
  assumption


example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  obtain ⟨⟨⟨p, s⟩, a⟩, ⟨_, ⟨⟨c, _⟩ , _⟩⟩⟩ := h
  constructor
  · assumption
  · constructor
    · assumption
    · constructor
      · assumption
      · assumption


example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  obtain ⟨⟨⟨p, s⟩, a⟩, ⟨_, ⟨⟨c, _⟩ , _⟩⟩⟩ := h
  exact ⟨a, c, p, s⟩
