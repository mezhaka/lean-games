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
Because the righthand side of h and the lefthand side of false_elim match, you can use imp_trans to combine these:

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
example (L : Prop) : ¬(L ∧ ¬L) := by
-- `¬(L ∧ ¬L)` is `(L ∧ ¬L) → False`
