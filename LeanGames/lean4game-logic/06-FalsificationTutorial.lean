import Mathlib.Logic.Basic
/-
In this world In this world, you'll be introduced to negation — which is written
with the “¬” symbol.

This operator is really just syntactic sugar. ¬P means P → False. It seamlessly
integrates into all the scenarios where implications are used. It's also
constructed using functions (λ...↦...) just like any other implication.

The new interesting element for this world is False. What is False? It's a
proposition — part of the set of statements that can be either true or false.
Importantly, however it's defined as a proposition which always happens to be
false. By sheer force of definition — there can never exist any evidence
supporting the veracity of False.

Consider a real-world analogue like “Tom is an experienced beginner” or “Tom is
a married bachelor”, neither can ever be true. For there to exist evidence of
either, you need to throw out definitions of the words themselves.

An interesting corollary arises: from the premise of False, any proposition
becomes permissible. If you're allowed to speak in gobbledygook, then you can
say anything!

Garbage In, Garbage out
Imagine you're signing a contract of utmost importance.  The terms stipulate:
“Once per day, you will be given a whole number greater than 0. If the number
falls below 100, you must gracefully wave your left hand; if it exceeds 90, your
right hand should elegantly sway. Lastly, if the number plunges below 0, you
must transform into a cucumber.”

On casual scrutiny, one might naively conclude that adhering to this contract
may involve turning into a cucumber. While that may seem impossible, a subtle
loophole exists. By astutely arguing that the contract will never demand the
impossible act of becoming a cucumber, you can effectively assure your
compliance.

By signing the contract, you're agreeing that “If there appears a number that is
both greater than 0 and less 0, then I will transform into a cucumber.” Your
grandiose claims remain secure as they hinge on an eventuality that defies
logical possibility.
-/

/- Level 1 / 12 : Not False
## Proof State
The proof state in the level is as short as you've seen so far. There are no
Objects or Assumptions listed.

In other levels, you get a proposition key and in the proof state — under
Objects — you'd see something like P Q : Prop. When you see P in a level, it's a
variable standing in for whatever proposition is in the proposition key. The
game freely re-uses these letters in other levels as they can stand in for
anything.

You won't see False listed under objects, just as you won't see Theorems or
Definitions listed under assumptions. This just means that False never changes
from level to level. It's never a stand-in for anything else. It's a fully
defined and always available proposition.

## Not False
Inuitively, it should be very simple to provide evidence for "not
false". Since ¬P is shorthand for P → False, you should think of ¬False as
shorthand for False → False. To drive home the fact that False is a proposition,
this has the same proof as P → P (Which you solved in "→ Tutorial, level 2").
-/
example : ¬False := by
  exact id


/-
You'll never actually find evidence for False, but evidence for ¬False is a very
simple tautology, as you would expect.
-/
example : ¬False := by
  exact λ(f : False) ↦ f


example : ¬False := by
  intro h
  exact h


/-
# Sybeth's Punctuality
Sybeth is never on time. Despite her assurances that she'll grace the party with
her timely presence, past experiences have proven otherwise. It's almost become
a running joke, so much so that you playfully quip, "Yeah, if you arrive on
time, then I'll eat my boots."

Proposition Key:
B — You eat your boots
S — Sybeth is on time

## false_elim
You've unlocked the "false implies anything" function. false_elim will take
evidence for False and produce evidence for anything.

## A Tip
Remember you can think of h : ¬S as h : S → False.

Once you've started with λ(s : S) ↦ , you'll then see that the expression h s
evaluates to evidence for False. If ever you have evidence for False, you should
aways immediatly consider using false_elim to create evidence for anything —
which in this case will be B.

There is no proof that "keeps going" once you've created evidence for False.
Some proofs have multiple parts, so you may close off one line of reasoning and
move on to another, but there can be no meaningfull logic in any context where
evidence for False is present.
-/
-- I use `False.elim` instead of `false_elim`.

-- Game constraints: use only `exact`, `have`, and the theorems.
example (B S : Prop)(h : ¬S) : S → B := by
  have from_s_false : S → False := h
  exact fun s => False.elim (from_s_false s)

/-
You've made use of the concept that "false implies anything".

h           : S     → False
false_elim  : False → B
Because the righthand side of h and the lefthand side of false_elim match, you
can use imp_trans to combine these:

imp_trans h false_elim
-/

-- No constraints soulution, I did first.
example (B S : Prop)(h : ¬S) : S → B := by
  intro s
  have b : B := False.elim (h s)
  exact b


/- Level 3 / 12 : Double False!
The Ambiguous Celebration Response
Your somewhat bothersome cousin just called and is asking if you're throwing
your annual soirée this year. You don't want to outright lie, so you say "I'm
not not throwing the party."

Proposition Key:
P — You're throwing a party'
-/
-- (Anton): I do not understand the problem statement above.
-- Game constraints: use only `exact`, `have`, and the theorems.
example (P : Prop)(p : P) : ¬¬P := by
-- (Anton): `¬¬ P` is `¬P → False`, which in turn is `(P → False) → False` ?!?!
  exact fun not_p => False.elim (not_p p)

-- No constraints soulution, I did first.
example (P : Prop)(p : P) : ¬¬P := by
  intro not_p
  exact False.elim (not_p p)


/- Level 4 / 12 : Self Contradictory
Self Contradictory
Alarfil claims Lippa is coming and Cyna claims Lippa is not coming. They can't
both be right.

Proposition Key:
L — Lippa is attending the party
-/
-- The law of non-self-contradiction
-- Game constraints: use only `exact`, `have`, and the theorems.
-- `¬(L ∧ ¬L)` is `(L ∧ ¬L) → False`
example (L : Prop) : ¬(L ∧ ¬L) := by
  exact fun lnl =>
    have nl : ¬L := lnl.right
    have l : L := lnl.left
    nl l


example (L : Prop) : ¬(L ∧ ¬L) := by
  intro h
  exact h.right h.left


/- Level 5 / 12 : Modus Tollens
Modus Tollens
If Bella comes to the party, she is certain to perform a bawdy song. You've
assured Sybeth that there will be no bawdy songs at the event. Sybeth is
disappointed to discover that Bella won't be joining.

Proposition Key:
B — Bella is attending the party
S — A bawdy song will be sung
-/
-- Game constraints: use only `exact`, `have`, and the theorems.
theorem modus_tollens (B S : Prop)(h1 : B → S)(h2 : ¬S) : ¬B := by
  exact fun b =>
    have false : False := h2 $ h1 b
    False.elim false

-- No constraints soulution, I did first.
example (B S : Prop)(h1 : B → S)(h2 : ¬S) : ¬B := by
  intro b  -- (Anton): I do not understand where intro pulled `b` from...
  -- I do now: the `¬B` to the right of the `:` is `B → False`, so `intro` gets me `B`.
  have false : False := h2 $ h1 b
  exact False.elim false

/-
Congradulations. Did you recognise this proof? It's actually a slightly less
general version of the proof you used in the "→ Tutotial world, level 4" to show
that implication is transitive.

Thinking of h₂ as Q → False, you can actually use your imp_trans theorem here.

exact λp ↦ h₂ (h₁ p)
exact imp_trans h₁ h₂
For the math-inclined, because the expression for an implication is a function,
you can also use function composition.

exact h₂ ∘ h₁
-/
example (B S : Prop)(h1 : B → S)(h2 : ¬S) : ¬B := by
  exact h2 ∘ h1

-- (Anton): Is there an imp_trans in Mathlib?
-- exact? gave me this:
example (A B C : Prop) (h1 : A → B) (h2: B → C) : A → C := by exact fun a ↦ h2 (h1 a)
-- so, looks like no--there's no such standard thing, although, I might miss some import.
-- I tried to `import Mathlib.Logic.Basic` and I get the same:
example (A B C : Prop) (h1 : A → B) (h2: B → C) : A → C := by exact fun a ↦ h2 (h1 a)


/- Level 6 / 12 : Alarfil
The Alarfil Effect
You're delighted that Alarfil will be there.

Remarkably, even in moments when Alarfil lacks humor, he manages to be amusing!
His comedic charm persists, regardless of circumstances.

Proposition Key:
A — Alarfil is humorless

Remember h : A → A → False
-/
example (A : Prop) (h: A → ¬A) : ¬A := by
  intro a
  have hf : A → False := h a
  exact hf a

example (A : Prop) (h: A → ¬A) : ¬A := by
  exact fun a => (h a) a


/- Level 7 / 12 : Negation
The Power of negation
"Is it possible that if this is the cake you bought, then it's gonna taste horrible?"
"I'm certain that's not possible."
"Oh, so what you're saying is that you have evidence that the cake is delicious!"

Proposition Key:
B — You bought this cake
C — The cake tastes horrible

Nested λ↦s.
-/
-- No constraints soulution, I did first.
example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  have hh : (B → C) → False := h
  intro c
  have b_to_c := fun b : B => c
  exact hh b_to_c


-- Game constraints: use only `exact`, `have`, and the theorems.
example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  exact fun c =>
    have b_to_c := fun b : B => c
    h b_to_c


/- Level 8 / 12 : Negated Conjunction
Definitely Not
Your cake order definitely has sprinkles, which means it's not missing sprinkles
and loaded with chocolate chips

Proposition Key:
C — The cake is loaded with chocolate chips
S — The cake is topped with sprinkles
Negation into conjuction.
-/
example (C S : Prop) (s: S) : ¬(¬S ∧ C) := by
  exact fun h : ¬S ∧ C =>
    have not_s : ¬S := h.left
    not_s s


/- Level 9 / 12 : Implies a Negation
Allergy #1
Owing to his allergy, if Pippin is present, there must be no avocado at the
party. Which means that we cannot have both Pippin and avacado at the party

Proposition Key:
A — There's avacado at the party
P — Pippin is attending the party
Show ¬(P ∧ A)
-/
example (A P : Prop) (h : P → ¬A) : ¬(P ∧ A) := by
  exact fun pa : P ∧ A =>
    have na : ¬A := h pa.left
    na pa.right


/- Level 10 / 12 : Conjunction Implicaiton
Allergy #2
We cannot have both Pippin and avacado at the party. Which means that if Pippin
is attending, then there will not be any avacado.

Proposition Key:
A — There's avacado at the party
P — Pippin is attending the party
Show P → ¬A.
-/

-- No constraints soulution, I did first.
example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  intro p a
  have h : (P ∧ A) → False := h
  have false : False := h (And.intro p a)
  exact false

-- Game constraints: use only `exact`, `have`, and the theorems.
-- I figured that I can use a `fun` with two variables by looking at my previous solution.
-- I was trying to make a nested lambda, but failed.
example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  exact fun (p : P) (a : A) => h (And.intro p a)

-- OK, here's the nested lambda, but I figured it kind of backwards, cause all Lean functions are
-- curried.
example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  exact fun (p : P) =>
          fun (a : A) => h (And.intro p a)

/-
That's settled... again!

Reminder that these are the same:

λp ↦ λa ↦ h ⟨p,a⟩
-- and
λp a ↦ h ⟨p,a⟩
-/
-- Interesting, one does not need a space after `λ`.
example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  exact λp ↦ λa ↦ h (And.intro p a)


/- Level 11 / 12 : not_not_not
Allergy: Triple Confusion
Pippin is allergic to avocado. You tell him you're not not not bringing
avacado!!! Pippin gives you a confused look, but after a moment of
contemplation, he responds with, "Ok, good to know."

Proposition Key:
A — You're bringing avacado
¬A is stable.
-/
-- (Anton): I struggled a lot with this one and asked ChatGPT in the end to show me.
example (A : Prop)(h : ¬¬¬A) : ¬A := by
  have h1 : ¬¬A → False := h
  have h2 : ¬(A → False) → False := h1
  have h3 : ((A → False) → False) → False := h2
  -- I was stuck at h3. Then I looked up the answer and realized one can write h4.
  -- However, it was not clear to me why `¬A → False ↔ ¬(A → False)`.
  have h4 : (¬A → False) → False := h3  -- (Anton) I do not get
  exact fun a ↦
    have na_to_false : ¬A → False := fun na : ¬A => na a
    h4 na_to_false

-- Compactify:
example (A : Prop)(h : ¬¬¬A) : ¬A := by
  exact λ a ↦ h (λ na ↦ na a)

example (A : Prop) : ¬A → False ↔ ¬(A → False) := by exact imp_false

example (A : Prop)(h : ¬¬¬A) : ¬A := by
  intro a
  -- Before `apply` the goal is `False`. `h` is `¬¬A -> False`. After apply the goal is `¬¬A`.
  -- (Anton): What I don't quite get is why do we need `intro a` to `apply h`...
  apply h
  intro na
  exact na a

/-
Level 12 / 12 : ¬Intro Boss
BOSS Level
"Is it possible that if this is the cake you bought, then it's gonna taste horrible?"
"I'm certain that's not possible!"
"Oh, so what you're saying is that you have evidence that this is not not the cake you bought."

Proposition Key:
B — You bought this cake
C — The cake tastes horrible
¬¬"You bought this cake"
-/
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  intro nb
  apply h
  exact fun b : B =>
    have f : False := nb b
    False.elim f


-- Game constraints: use only `exact`, `have`, and the theorems.
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  exact fun nb =>
    have h1 : (B → C) → False := h
    have b_to_c : B → C := fun b => False.elim (nb b)
    h1 b_to_c


-- Compactify:
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  exact λ nb ↦ h (λ b ↦ False.elim (nb b))


-- exact? solution
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  exact not_not_of_not_imp h

/-
Level completed! 🎉
These unintuitive statements highlight the inherent challenge in contemplating
the potential existence (or definite non-existance) of implications.

That's a twist of logic, to be sure!
-/

------- I wanted to see how is P ∨ ¬P is handled in Lean.
theorem excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P

#print axioms excluded_middle
-- 'excluded_middle' depends on axioms: [propext, Classical.choice, Quot.sound]
#check propext
#check Classical.choice
#check Quot.sound
----------
