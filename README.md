# Automated Theorem Proving

In 1958 the logician Hao Wang implemented one of the first automated theorem provers. He succeeded in writing several programs capable of automatically proving a majority of theorems from the first five chapters of Whitehead and Russell's *Principia Mathematica* (in fact, his program managed to prove over 200 of these theorems "within about 37 minutes, and 12/13 of the time is used for read-in and print-out"). This  was an impressive achievement at the time; previous attempts had only succeeded in proving a handful of the theorems in *Principia Mathematica*.

## Background

Wang's idea is based around the notion of a *sequent* (this idea had been introduced years earlier by Gentzen) and the manipulation of sequents. A sequent is essentially a list of formulae on either side of a sequent (or provability) symbol $\vdash$. The sequent $\pi \vdash \rho$, where $\pi$ and $\rho$ are strings (i.e., lists) of formulae, can be read as "the formulae in the string $\rho$ *follow* from the formulae in the string $\pi$" (or, equivalently, "the formulae in string $\pi$ prove the formulae in string $\rho$").

To prove whether a given sequent is true all you need to do is start from some basic sequents and successively apply a series of rules that transform sequents until you end up with the sequent you desire. This process is detailed below.

Additionally, determining whether a formula $\phi$ is a theorem, is equivalent to determining whether the sequent $\empty \vdash \rho$ is true (e.g. $\vdash \neg \empty \lor \rho$).

### Formulae

#### Connectives

We allow the following connectives in decreasing order of precedence:

$\neg$ : negation

$\land$ : conjunction; $\lor$ : disjunction (both same precedence)

$\rightarrow$ : implication; $\leftrightarrow$ :biconditional (both same precedence).

#### Connectives

- A propositional symbol (e.g., p, q, ...) is an atomic formula (and thus a formula).
- If $\phi$, $\psi$ are formulae, then $\neg \phi$, $\phi \land \psi$, $\phi \lor \psi$, $\phi \rightarrow \psi$, $\phi \leftrightarrow \psi$  are formulae.

#### Sequent

If $\pi$ and $\rho$ are strings of formulae (possibly empty strings) and $\phi$ is a formula, then $\pi, \phi, \rho$ is a string and $\pi \vdash \rho$ is a sequent.

### Rules

The logic consists of the following sequent rules. The rst rule (P1) gives a characterisation of simple theorems. The remaining rules are simply ways of transforming sequents into new sequents. The manner in which you can construct a proof for a sequent to determine whether it holds or not is given below.