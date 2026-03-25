#Proposition Rules

In file `Proposition Rules.v` we introduce tactics that we will use for deduction in propostion logic.

It consists of the following parts:

- Tactics for dealing with `Proof Context`

- Itroduction and Elimination tactics for the following constants and connectictives for Intuitionistic Logic:
  - `True` and `False`
  - `Implication` (→)
  - `And` (∧)
  - `Or` (∨)
  - `Biconditional` (↔)
  - `Negation` (¬)

- The tactic, addition of which turns Intuitionistic Logic into Classical Logic

Your task is to prove all the propostional tautologies in `Task.v`, using these tactics.

After each prove you should change each `Admitted` to `Qed`.

You can find solution in `Solution.v`
