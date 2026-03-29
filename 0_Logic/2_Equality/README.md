# Equality Rules

We finish studying [Natural Deduction](https://en.wikipedia.org/wiki/Natural_deduction#Gentzen-style_propositional_logic).

In coq and my `Top.TacticNames` library, there are speicific tactics to work
with Equality.

These tactics together make `Normal` Definition of `Equality`.

Thoroughly study all examples in `EqualityRules.v`

They show, how the equality tactics can be used in the most general and, on other hand, simple way.

Tactics consists of the following parts:

- `Itroduction` rules for `Equality` (=)

- `Elimination` rules for `Equality` (=) in `rewrite`/ `replace` form

- `Classical` `Introduction` rules for `Prop` `Equality`

First two parts are already default `Coq` tactics.

I tried to include both `Forward` (enriching the `Context`) and `Backward` (simplifying the `Goal`) reasoning for the `third` part.

Note, that the rules from the `first two` rules can be used both in the `Intuitionistic` and `Classical` Logic.

While the third rule (`Introduction` rules for `Prop` `Equality`) is usually added only for the `Classical` Logic. Sometimes, it is not even included for the `Classical` Logic.

Your task is to prove all the quantifier validities in `Task.v`, using these tactics.

If a theorem has `_cl` suffix in its name, it means it requires classical rules.
If a theorem doesn't have this suffix, it means, that you should try to prove it without using any of classical rules.

After each prove you should change each `Admitted` to `Qed`.

You can use theorems from previous tasks.
For more detail on that look in README in the root.

You can find solution in `Solution.v`.

P.S

Remember very important requirements, when working with `Top.TacticNames`:

In !!ANY!! file, which uses `Top.TacticNames` tactic library
you CAN'T name hypothesis, starting with underscore `_`.

This requirement is assumed to be strictly met.
Otherwise you will have UNDEFINED BEHAVIOUR.
