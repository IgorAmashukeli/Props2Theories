# Quantifier Rules

We continue studying [Natural Deduction](https://en.wikipedia.org/wiki/Natural_deduction#Gentzen-style_propositional_logic).

In my `Top.TacticNames` library, I also defined useful list of tactics
for dealing with predicate and quantifier logic.

They reflect the theoretically defined rules for quantifiers on predicates in `Natural Deduction`.

Thoroughly study all examples in `Quantifier Rules.v`

They show, how the tactics from `Top.TacticNames` library can be used in the most general and, on other hand, simple way.

Tactics consists of the following parts:

- `Itroduction` and `Elimination` tactics for the following quantifiers on predicates:
  - `Universal Quantifier` (∀)
  - `Existential Quantifier` (∃)

I tried to include both `Forward` (enriching the `Context`) and `Backward` (simplifying the `Goal`) reasoning for convinience in different situations.

Note, that all this tactic rules are defined both in `Intuitionistic` and `Classical`
Predicate Logic.

Note, that we use default arrow type `T → Prop` as Coq primitive for Predicates.

Your task is to prove all the quantifier validities in `Task.v`, using these tactics.

If a theorem has `_cl` suffix in its name, it means it requires classical rules.
If a theorem doesn't have this suffix, it means, that you should try to prove it without using any of classical rules.

After each prove you should change each `Admitted` to `Qed`.

You can find solution in `Solution.v`

P.S

Remember very important requirements, when working with `Top.TacticNames`:

In !!ANY!! file, which uses `Top.TacticNames` tactic library
You CAN'T name hypothesis, starting with underscore `_`.

This requirement is assumed to be strictly met.
Otherwise you will have UNDEFINED BEHAVIOUR.
