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

**P1** Initial Rule: If $\lambda, \zeta$ are strings of atomic formulae, then $\lambda \vdash \zeta$ is a theorem if some atomic formula occurs on both side of the sequent $\vdash$.

In the following ten rules  and  are always strings (possibly empty) of formulae.

**P2a** Rule $\vdash \neg$: If $\phi, \zeta \vdash \lambda, \rho$, then $\zeta \vdash \lambda, \neg \phi, \rho$

**P2b** Rule $\neg \vdash$: If $\lambda, \rho \vdash \pi, \phi$, then $\lambda, \neg \phi, \rho \vdash \pi$

**P3a** Rule $\vdash \land$: If $\zeta \vdash \lambda, \phi, \rho$ and $\zeta \vdash \lambda, \psi, \rho$, then $\zeta \vdash \lambda, \phi \land \psi, \rho$

**P3b** Rule $\land \vdash$: If $\lambda, \phi, \psi, \rho \vdash \pi$, then $\lambda, \phi \land \psi, \rho \vdash \pi$

**P4a** Rule $\vdash \lor$: If $\zeta \vdash \lambda, \phi, \psi, \rho$, then $\zeta \vdash \lambda, \phi \lor \psi, \rho$

**P4b** Rule $\lor \vdash$: If $\lambda, \phi, \rho \vdash \pi$ and $\lambda, \psi, \rho \vdash \pi$ then $\lambda, \phi \lor \psi, \rho \vdash \pi$

**P5a** Rule $\vdash \rightarrow$: If $\zeta, \phi \vdash \lambda, \psi, \rho$, then $\zeta \vdash \lambda, \rho \vdash \psi, \rho$

**P5b** Rule $\rightarrow \vdash$: If $\lambda, \psi,\rho \vdash \pi$, and $\lambda, \rho \vdash \pi, \phi$, then $\lambda, \phi \rightarrow \psi, \rho \vdash \pi$

**P6a** Rule $\vdash \leftrightarrow$: If $\phi, \zeta \vdash \lambda, \rho$, and $\psi, \zeta \vdash \lambda, \phi, \rho$, then $\zeta \vdash \lambda, \phi \leftrightarrow \psi, \rho$

**P6b** Rule $\leftrightarrow \vdash$: If $\phi, \psi, \lambda, \rho \vdash \pi$, and $\lambda, \rho \vdash \pi, \phi, \psi$, then $\lambda, \phi \leftrightarrow \psi, \rho \vdash \pi$

### Proofs

The basic idea in proving a sequent $\pi \vdash \rho$ is to begin with instance(s) of Rule P1 and successively apply the remaining rules until you end up with the sequent you are hoping to prove.

For example, suppose you wanted to prove the sequent $\neg(p \lor q) \vdash \neg p$. One possible proof would proceed as follows.

1. $p \vdash p, q$						Rule 1
2. $p \vdash p \lor q$					Rule P4a
3. $\vdash \neg p, p \lor q$					Rule P2a
4. $\neg (p \lor q) \vdash \neg p$				Rule P2b

However, a simpler idea (as it will involve much less search) is to begin with the sequent(s) to be proved and apply the rules above in the \backward" direction until you end up with the sequent you desire. In the example then, you would begin at step 4 and apply each of the rules in the backward direction until you end up at step 1 at which point you can conclude the original sequent is a theorem.

## Code Specication

This code intends to emulate Hao Wang's feats and implement a propositional theorem prover.

### Input

The input will consist of a single sequent on the command line. Sequents will be written as: [*List of Formulae*] seq [List of Formulae] To construct formulae, atoms can be any string of characters (without space) and connectives as follows:

- $\neg$: neg
- $\land$: and
- $\lor$: or
- $\rightarrow$: imp
- $\leftrightarrow$: iff

So, for example, the sequent $p \rightarrow q, \neg r \rightarrow \neg q \vdash p \rightarrow r$ would be written as:

​	[p imp q, (neg r) imp (neg q)] seq [p imp r]

The code prover should be excuted as follows: 

​	./prover.py 'Sequent'

For example 

​	./prover.py '[p imp q, (neg r) imp (neg q)] seq [p imp r]'

### Output

The first line of the output will be either true or false indicating whether or not the sequent on the command line holds. The subsequent lines of output should produce a proof like the one in the *Proofs* section above.

## References

[1]: https://ieeexplore.ieee.org/abstract/document/5392526	"Hao Wang, Toward Mechanical Mathematics, IBM Journal for Research and Development, volume 4, 1960 (Reprinted in: Hao Wang, &quot;Logic, Computers, and Sets&quot;, Sciene Press, Peking, 1962. Hao Wang, &quot;A Survey of Mathematical Logic&quot;, North Holland Publishing Company, 1964. Hao Wang, &quot;Logic, Computers, and Sets&quot;, Chelsea Publishing Company, New York, 1970.)"
[2]: https://plato.stanford.edu/entries/principia-mathematica/	"Alfred North Whitehead and Bertrand Russell, Principia Mathematica, 2nd Edition, Cambridge"

