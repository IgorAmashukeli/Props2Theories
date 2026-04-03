# Proposition Rules

[Natural Deduction](https://en.wikipedia.org/wiki/Natural_deduction#Gentzen-style_propositional_logic) is one of the most common and convinient underlying systems for formal proof in Math.

In my `TacticNames.lean` file, I defined useful list of tactics
for dealing with propositional logic.

They reflect the theoretically defined rules in `Natural Deduction`.

Thoroughly study all examples in `Proposition Rules.v`

They show, how the tactics from `Top.TacticNames` library can be used in the most general and, on other hand, simple way.

Tactics consists of the following parts:

- Tactics for dealing with `Proof Context`

- `Itroduction` and `Elimination` tactics for the following constants and connectictives for `Intuitionistic Logic`:
  - `True Itroduction` and `False Elimination`
  - `Implication` `Itroduction` and `Elimination` (→)
  - `Conjunction` `Itroduction` and `Elimination` (∧)
  - `Disjunction` `Itroduction` and `Elimination` (∨)
  - `Logical Equivalence` `Itroduction` and `Elimination` (↔)
  - `Negation` `Itroduction` and `Elimination` (¬)

- `ByContradiction` Tactics, addition any of which turns `Intuitionistic Logic` into `Classical Logic`.

I tried to include both:

- `Forward` (enriching the `Context`)
- `Backward` (simplifying the `Goal`)
  reasoning for convinience in different situations.

Note, that we use default `Prop` type as Coq primitive for Propositions.

Before continuing, read very important requirements, explained in P.S below.

Your task is to prove all the propostional tautologies in `Task.lean`, using these tactics.

If a theorem `has _cl suffix` in its name, it means it `requires` `Classical` rules.

If a theorem `doesn't have this suffix`, it means, that you should try to prove it `without using any of Classical` rules.

After each prove you should change each `sorry` to prove.

You can find solution in `Solution.lean`

P.S

In !!ANY!! file, which uses `TacticNames` tactic import
you CAN'T name hypothesis, starting with underscore `_`.

This requirement is assumed to be strictly met.
Otherwise you will have UNDEFINED BEHAVIOUR.
