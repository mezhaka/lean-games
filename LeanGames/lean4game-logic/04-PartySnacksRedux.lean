-- Level 1 / 9 : Apply
example (P Q: Prop)(h'₁: P)(h : P → Q) : Q := by
  apply h
  exact h'₁


example (P Q: Prop)(h'₁: P)(h : P → Q) : Q := by
  apply h
  assumption



-- Level 2 / 9 : Identity
/-The intro Tactic
The intro tactic lets you define a function interactively. It introduces one or more hypotheses, optionally naming them.

In this level, intro h does two things. First, it adds an assumption h : P and second, it changes your goal from P → P to just P. In this sense, intro h is a bit like λh ↦ .
-/

example (P: Prop) : P → P := by
  intro p
  assumption


-- Level 3 / 9 : Swapping
example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro pq
  -- Q (Anton): cases is suppossed to work on inductive type, but `pq` is a structure. How do I destructure `pq`?
  cases pq
  · constructor
    · assumption
    · assumption


example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro pq
  constructor
  cases pq
  assumption
  cases pq
  assumption


example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro pq
  cases pq


-- Level 4 / 9 : Apply Chain Reasoning
-- (Anton): It feels I did not solve it as it is intended.
example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  -- have h : C → S := h2 ∘ h1
  apply h2 ∘ h1


-- Level 5 / 9 : Apply Backwards
-- (Anton): It feels I did not solve it as it is intended.
example (P Q R S T U: Prop) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : P → U := by
  apply h5 ∘ h3 ∘ h1


-- Level 6 / 9 : repeat combinator
/-
Breakthrough! (Anton): I used `apply` before, but this example has put things in place: the goal
is to show `P → Q → R`, which means we can introduce `p` and `q` and the goal becomes `R`. Then
one can see that we have an assumption `(P ∧ Q) → R`, which means that in order to show `R` it
suffices to show `P ∧ Q`, which we do below.
-/
example (P Q R: Prop) (h : P ∧ Q → R) : P → Q → R := by
  intro p q
  apply h
  constructor
  repeat assumption


-- Level 7 / 9 : Another One
def myand (P Q : Prop) (p : P) (q : Q) := And.intro p q

example (P Q R: Prop) (h : P → Q → R) : P ∧ Q → R := by
  intro pq
  -- Here `cases` has only one case, cause `P ∧ Q` is a structure.
  · cases pq with
    | intro p q =>
      apply h
      · assumption
      · assumption


-- I do not remember which level it is.
example (P Q R: Prop) (h : P ∧ Q → R) : (P → Q → R) := by
  intro p q
  -- Why the target changes from `P → Q → R` to `R` after the `intro p q`. I think I have trouble understanding
  -- chained implication, like `a → b → c → d`. It seems in this conext `P → Q → R` can be thought of as a graph
  -- wich looks like `P → Q ← R`. So `P` and `Q` are independent, but the notation `P → Q → R` seems to imply that
  -- we need to "move" from `P` to `Q`, which is not "true" if we already have the evidence `p` and `q`.
  have r := h (And.intro p q)
  exact r


-- Level 8 / 9 : Distribute
example (P Q R : Prop) (h : (P → Q) ∧ (P → R)) : P → Q ∧ R := by
  intro p
  cases h with
  | intro pq pr =>
    apply And.intro
    · apply pq
      assumption
    · apply pr
      assumption


example (P Q R : Prop) (h : (P → Q) ∧ (P → R)) : P → Q ∧ R := by
  intro p
  cases h with
  | intro pq pr =>
    apply And.intro
    · exact pq p
    · exact pr p


-- Level 9 / 9 : Implication Tactic Boss
example (P Q : Prop) : Q → (P → Q) ∧ (¬P → Q) := by
  intro q
  constructor
  repeat {intro; assumption}
