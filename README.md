# Props2Theories

## Common words about the repository:

This course covers the most significant foundations, core knowledge and applications for math (sometimes with reference to Pure Math, sometimes with reference to Theoretical Computer Science).

The course structure in this repository closely resembles that of my Voltage2Services course.

The difference is, this not about programming, it is about math.

It explains the basics of math, starting from the logic and set axioms and proceeding to basic abstractions of pure math and theoretical computer science applications.

But it is much deeper and at a higher level than many well-known courses.

Let's call this Props2Theories.

For this course, all fundamental main math course objects and theorems about them (with solution proofs) will be added, so the course will change. 

It will be in progress for a long time.

## Course structure

The course consists of different math subjects.

Each subject is divided into different topics.

The two compulsory subjects are Logic and Set Theory:

    - The first Logic subject starts with high-order deduction rules. It is given in Rules.lean file

    - The second subject Set Theory starts by ZFC set theory axioms.

Using axioms as default theorems and rules for deductions as rule games,
you can build all the needed math fundamentals:

    - The definitions will be build upon this for you
    - Your task is to prove the list of theorems for each topic in Task.lean
    - In each topic you will also find solution in Solution.lean

The course is structured in such a way that you usually need only knowledge from the previous tasks, plus your creativity and ability to carefully build the proofs.

## Technical instructions:

For all the software needed to be installed it is LEAN 4.

1) Install VS CODE
2) Install VS CODE LEAN 4 extension
3) Follow the rules for the further LEAN 4 installation, that would be given to you after extension is installed.
4) To make sure it works, restart any file you need to make working
5) You can see that LEAN 4 accepts and compiles all the proofs
6) If you point at any point of the proof and toggle InfoView, you will see all the current context
(Objects and theorem variables)

I simply expect you to use Linux (mine is Fedora), but usually, it can also be installed on macOS and Windows. But it is your responsibility to install VS CODE, LEAN4

## About the choice of fundamentals

I know that CIC Type Theory math foundamentals is more convinient in LEAN and consists of many given fundamentals in language or library.
Moreover, together with lambda calculus, it allows for much more convinient computable reductions of some arithmetic.
Also, Coq and Lean complex tactics also can help for some trivial, but tedious proofs.
You also can argue that, axiomatic structure of ZFC Theory is not the most natural way for LEAN, which follows constructive logic.


But, however in this repository I want you to experience the hardcore way. 
It is useful to know, how you can build math abstractions from abstract Logic rules and Set Theory axioms with some non-trivial constructions.

Have fun! 😈

## P.S

If you really want to learn about such topics as:

- Simple functional programming fundamentals, including lambda calculus
- Type theories
- Verificators

and build your own compilers for different functional languages such as:
- Untyped
- Haskell-like
- Coq/Lean like

you can study 04_Functional chapter of my another comprehensive Voltage2Services programming course

