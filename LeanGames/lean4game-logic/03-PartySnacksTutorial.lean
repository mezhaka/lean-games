-- Level 3 / 9 : Cake Form Swap
/-
Trouble with the cake
The baker from the bakery called, expressing confusion about your cake order. While he can bake a cake with icing and sprinkles, you've requested sprinkles and icing. You attempt to convey that every cake with sprinkles and icing is also at the same time a cake with icing and sprinkles. The baker doesn't believe you.

If you assume an arbitrary cake that has icing and that has sprinkles, show that you also have a cake that has sprinkles and has icing!

Proposition Key:
I — The cake has Icing
S — The cake has Sprinkles
-/
example (I S: Prop) : I ∧ S → S ∧ I := by
  exact λ h : I ∧ S ↦ And.intro h.2 h.1


example (I S: Prop) : I ∧ S → S ∧ I := by
  exact λ h  ↦ ⟨h.2, h.1⟩


-- Level 4 / 9 : Chain Reasoning
example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  exact λ c ↦ h2 (h1 c)


-- Level 5 / 9 : Riffin Snacks
example (P Q R S T U: Prop) (p : P) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : U := by
  exact h5 (h3 (h1 p))

-- Q (Anton): It seems `≫` is not available here.
-- example (P Q R S T U: Prop) (p : P) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : U := by
--   exact (h₁ ≫ h₃ ≫ h₅) p

/- Level 6 / 9 : and_imp. Conjunction interacting with implication.
Curry
If you've got chips and dip, then you've got a popular party snack! This is undeniable.

Therefore if you've got chips, then if you've got dip, then you've got a popular party snack.

Proposition Key:
C — You've got chips
D — You've got Dip
S — You've got a popular party snack
-/
example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  intro c d
  have s := h (And.intro c d)
  exact s


-- ChatGPT
example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  have h1 : ∀ c d, C ∧ D := λ c d => ⟨c, d⟩
  exact λ c d => h (h1 c d)


-- Simplified ChatGPT
example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  exact λ c d => h ⟨c, d⟩


/-
→ intro

fun _ => _
You can create evidence for an implication by defining the appropriate function.

have h₁ : P → P := fun p : P => p
have h₂ : P ∧ Q → P := fun h : P ∧ Q => h.left
Generally, you don't need to repeat the types when they're obvious from the context.

have h₁ : P → P := fun p => p
have h₂ : P ∧ Q → P := fun h => h.left
Unicode:
fun can be written as λ
=> can be written as ↦
have h₁ : P → P := λp ↦ p
have h₂ : P ∧ Q → P := λh ↦ h.left
-/
example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  have (fun cd => s) := h
  exact λ t : (C → D) => h.left ⟨c, d⟩



-- Level 7 / 9 : and_imp 2
-- (Anton): I would not be able to figure it out without our class.
example (C D S: Prop) (h : C → D → S) : C ∧ D → S := by
  exact fun cd => (h cd.left) cd.right


-- Level 8 / 9 : Distribute
example (C D S : Prop) (h : (S → C) ∧ (S → D)) : S → C ∧ D := by
  exact fun s => ⟨h.left s, h.right s⟩


example (C D S : Prop) : (S → C) ∧ (S → D) → (S → C ∧ D) := by
  intro h
  exact fun s => ⟨h.left s, h.right s⟩


-- Level 9 / 9 : Uncertain Snacks
example (R S : Prop) : R → (S → R) ∧ (¬S → R) := by
  exact fun r => And.intro (fun s : S => r) (fun ns : ¬S => r)


------------------ Redux ------------------------
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
