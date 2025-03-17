/- (Anton) For some reason `lemma` gives me an error:
unexpected identifier; expected commandLean
-/
theorem or_elim {P Q R : Prop} (h : P ∨ Q) (left : P → R) (right : Q → R) : R := by
  cases h with
  | inl p => exact left p
  | inr q => exact right q

theorem or_inl {P Q} (p : P) : P ∨ Q := by
  exact Or.inl p

theorem or_inr {P Q} (q : Q) : P ∨ Q := by
  exact Or.inr q

/- Level 3 / 8 : Or Elimination
Party Games
Here's the deal. Ilyn and Cyna both said they're bringing board games and you're sure at least one of them is going to make it. So there's definitely board games at the party!

Proposition Key:
B — There will be boardgames at the party
C — Cyna is coming to the party
I — Ilyn is coming to the party
Or Elimination
If you can conclude something from A and you can conclude the same thing from B, then if you know A ∨ B it won't matter which of the two happens as you can still guarentee something.

You've unlocked or_elim
or_elim has three parameters:

takes evidence for a disjunction,
evidence an implication on the left,
evidence for an implication on the right.
or_elim is your first 3-paramater function. The associated proposition is or_elim : (P ∨ Q) → (P → R) → (Q → R) → R.

pvq: P ∨ Q
pr : P → R
qr : Q → R
have r : R := or_elim pvq pr qr
-/
example (B C I : Prop) (h1 : C → B) (h2 : I → B) (h3 : C ∨ I) : B := by
  exact or_elim h3 h1 h2


/- Level 4 / 8 : Or is Commutative
(Anton): I could not figure the solution without the `cases` on my own, but ChatGPT
could.
I think this is a very important example, cause I failed to see that I could have built
the evidence. I was looking at `or_elim` and I could see that I one of the arguments,
the `∨` part, but I did not "unwrap" that in my case `R` is `O ∨ C`. If I reason
backwards, I can do this: `R` is `O ∨ C`, then the evidence for `or_elim` should be
of type `C → O ∨ C` and `O → O ∨ C`. Then I would probably stuck again, cause I still
forget that implication is built with a lambda.
-/
example (C O : Prop) (h : C ∨ O) : O ∨ C := by
  have h1 : (C → O ∨ C) := fun c => Or.inr c
  have h2 : (O → O ∨ C) := fun o => Or.inl o
  exact or_elim h h1 h2


example (C O : Prop)(h : C ∨ O) : O ∨ C := by
  cases h with
  | inl c => exact Or.inr c
  | inr o => exact Or.inl o


/- Level 5 / 8 : Carry On Effects
Carry On Effects
If the cake arrives, then everybody will rejoice. Either the cake arrives or you get a refund. Therefore, either everybody will rejoice or you get a refund! That's a win-win situation.

Proposition Key:
C — The cake arrives
J — Everybody is joyfull
R — You get a refund
-/
-- No game constraint solution, I came up with first.
example (C J R : Prop)(h1 : C → J)(h2 : C ∨ R) : J ∨ R := by
  cases h2 with
  | inl c => exact Or.inl (h1 c)
  | inr r => exact Or.inr r

-- Game constraints: use only `exact`, `have`, and the theorems.
example (C J R : Prop)(h1 : C → J)(h2 : C ∨ R) : J ∨ R := by
  have l : (C → J ∨ R) := fun c => Or.inl (h1 c)
  have r : (R → J ∨ R) := fun r => Or.inr r
  exact or_elim h2 l r


/- Level 6 / 8 : or distributes over and
A distribution of cookies
You can tell the cookies are either gingersnap cookies or they're a mix of shortbread cookies and sugar cookies.

Proposition Key:
G — They are gingersnap cookies
H — They are shortbread cookies
U — They are sugar cookies
-/
-- (Anton): I find the human readable example hard to get.
--
-- Game constraints: use only `exact`, `have`, and the theorems.
example (G H U : Prop)(h : G ∨ H ∧ U) : (G ∨ H) ∧ (G ∨ U) := by
  have l : G → (G ∨ H) ∧ (G ∨ U) := fun g => And.intro (Or.inl g) (Or.inl g)
  have r : H ∧ U → (G ∨ H) ∧ (G ∨ U) := fun hu => And.intro (Or.inr hu.left) (Or.inr hu.right)
  exact or_elim h l r


example (G H U : Prop)(h : G ∨ H ∧ U) : (G ∨ H) ∧ (G ∨ U) := by
  cases h with
  | inl g => exact And.intro (Or.inl g) (Or.inl g)
  | inr hu => exact And.intro (Or.inr hu.left) (Or.inr hu.right)


/- Level 7 / 8 : and distributes over or
A distribution of cookies
You can tell from the aroma that there are are gingersnap cookies. There's another smell there too. Could be shortbread cookies or sugar cookies.

Proposition Key:
G — They are gingersnap cookies
H — They are shortbread cookies
U — They are sugar cookies
-/
-- ∧ over ∨
-- Game constraints: use only `exact`, `have`, and the theorems.
-- (Anton): How do I show `∨` ?
example (G H U : Prop)(h' : G ∧ (H ∨ U)) : (G ∧ H) ∨ (G ∧ U) := by
  have g := h'.left
  have h_or_u := h'.right
  -- (Anton): It feels, like I have constructed it purely relying on types. I do not really understand what it "means"
  -- to use `g` from the outer scope in `fun` defenitions below.
  have fh : H → (G ∧ H) ∨ (G ∧ U) := fun h => Or.inl (And.intro g h)
  have fu : U → (G ∧ H) ∨ (G ∧ U) := fun u => Or.inr (And.intro g u)
  exact or_elim h_or_u fh fu


example (G H U : Prop)(h : G ∧ (H ∨ U)) : (G ∧ H) ∨ (G ∧ U) := by
  have g := h.left
  have h_or_u := h.right
  cases h_or_u with
  | inl h => exact Or.inl (And.intro g h)
  | inr u => exact Or.inr (And.intro g u)


/- Level 8 / 8 : The Implication
BOSS LEVEL
If we summon the Kraken, then we shall assuredly perish. While that might sound ominous, consider this: if we summon the Kraken or have icecream, then we shall have icecream! or we shall perish.

Proposition Key:
I — We have have icecream!
K — We summon the Kraken
P — We shall assuredly perish
-/
-- Implication of ∨
-- Game constraints: use only `exact`, `have`, and the theorems.
example (I K P : Prop)(h : K → P) : K ∨ I → I ∨ P := by
  have fi : I → I ∨ P := fun i => Or.inl i
  have fk : K → I ∨ P := fun k => Or.inr (h k)
  exact fun k_or_i => or_elim k_or_i fk fi


example (I K P : Prop)(h : K → P) : K ∨ I → I ∨ P := by
  intro k_or_i
  cases k_or_i with  -- (Anton) How do we ensure those are all cases there are?
  | inl k => exact Or.inr (h k)
  | inr i => exact Or.inl i
