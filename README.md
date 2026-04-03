# Props2Theorems

## Common words about the repository:

This course covers the most important foundations, core knowledge, and applications of mathematics (sometimes with reference to Pure Math, and sometimes to Theoretical Computer Science).

The course structure in this repository closely resembles that of my Voltage2Services course.

The difference is that this is not about programming; it is about mathematics.

It explains the basics of math, starting from logic and set axioms and proceeding to fundamental abstractions in pure math and applications in theoretical computer science.

However, it goes much deeper and is at a higher level than many well-known courses.

Let's call this Props2Theories.

For this course, all fundamental mathematical objects and theorems about them (with full solution proofs) will be added, so the course will evolve over time.

It will be a long-term work in progress.

## Course structure

The course consists of different mathematical subjects.

Each subject is divided into multiple topics.

- Your task is to prove the listed theorems for each topic in `Task.lean`.
- In each topic, you will also find solutions in `Solution.lean`.

The course is structured in such a way that you usually only need knowledge from previous tasks, along with your creativity and ability to carefully construct proofs.

## Technical instructions:

The required software to install includes Coq, opam, and vsrocq.

1. Install `VS Code`.
2. Install the VS Code extension `lake`, `lean`, `elan`
3. Install `Lean 4` VS Code extension

Look up installation instructions online for your system.

4. The root directory contains `Props2Theories` subdirectory,
   we will work there

5. `ChapterOrder.md` file lists the order of chapters

6. We will use my `TacticNames.lean` and `Axioms.lean` files

I generally expect you to use Linux (I use Fedora), although it can usually also be installed on macOS and Windows. However, it is your responsibility to install VS Code, vsrocq, etc.

## About the choice of fundamentals

We will use:

1. `Natural Deduction` rules, defined as tactics in the `TacticNames.lean` file

- Rules for `Propositional Logic` (`Intuitionistic` + `Classical`)
- Rules for `Higher-Order Predicate Logic`
- Rules for `Equality`

2. `℩` (the `iota operator`) for `Definite Descriptions` in the `Axioms.lean` file

3. `ZF` axioms, defined in `Axioms.lean` file

4. Sometimes (not always), we will use the `Axiom of Choice` or even the `Tarski Axiom`, both of which are also defined `Axioms.lean`

All mathematics will be built upon these four foundations.

So, we will essentially work within three different `Set Theory` systems:

- `ZF`
- `ZFC` (`ZF` + the `Axiom of Choice`)
- `TG` (`ZF` + the `Axiom of Choice` + the `Tarski Axiom`)

Here, `ZFC` is an extension of `ZF`, and `TG` is an extension of `ZFC`.

I am aware that `CIC` (`Calculus of Inductive Constructions`) as a mathematical foundation is more convenient in LEAN and includes many built-in primitives in the language or libraries.

Moreover, together with lambda calculus, it allows for much more convenient computable reductions of certain expressions (for example, in arithmetic).

Also, in Lean or in other proof assistants (such as `Coq`), there are advanced tactics that can simplify some trivial but tedious proofs.

We could even have chosen `HoTT` (`Homotopy Type Theory`) as the foundational system.

You could also argue that the axiomatic structure of our theories is not the most natural fit for Lean, which primarily follows constructive logic.

However, in this repository, I explicitly want you to experience the "hardcore" approach.

It is useful to understand how to build mathematical abstractions from abstract `Logic Rules` and `Set Theory Axioms` using non-trivial ideas.

Have fun! 😀

## P.S

If you really want to learn about topics such as:

- Basic functional programming fundamentals, including lambda calculus
- Type theories
- Proof assistants

and build your own compilers for different functional languages such as:

- Untyped
- Haskell-like
- Lean/Coq/Agda-like

you can study the `Functional` chapter of my other comprehensive Voltage2Services course, which teaches functional programming and type theory.
