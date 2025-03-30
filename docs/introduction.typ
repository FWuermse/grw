#import "./template.typ": *
#import "./theme.typ": *

= Introduction <Introduction>

Rewriting in theorem provers is the process of replacing a subterm $t$ of inside an expression with another term $u$. In Lean, rewriting is possible when the two terms are equal $t = u$ or when the two terms are propositions and imply each other $p <-> q$. This allows us to replace a term in a goal we want to solve or inside one of our hypothesis when reasoning in Lean.

We can use the `rewrite` tactic in lean to show the that two natural numbers are still then same when we add zero on one side. Consider the example theorem $1 = 1 + 0$ that we want to proof. We also assume that we have a hypotheses that states $forall n : NN, n + 1 = n$. We can then perform a left-to-right rewrite. By that we mean replacing occurrences of the left-hand-side of the theorem ($n + 1$) in the proof-goal with the right-hand-side of that theorem. Using this rewrite we can alter the original goal $1 = 1 + 0$ to $1 = 1$ because $1 + 0$ is an occurrence of our theorems left-hand-side. The following example represents the rewrite in Lean's syntax:

#show raw.where(block: true): code => {
  show raw.line: line => {
    let max = int(calc.log(line.count));
    let zeroes = range(max - int(line.number / 10));
    text(fill: gray)[#zeroes.fold("", (c, i) => c + " ")#str(line.number)]
    h(1em)
    line.body
  }
  code
}

```lean
example (h : ∀ n : Nat, n + 0 = n) : 1 = 1 + 0 := by
  rewrite [h]
  rfl
```

The syntax for rewriting in Lean is the keyword `rewrite` followed by a list of rewrite theorems. By appending the `at` keyword in sequence with a hypotheses we can rewrite the hypotheses istead of the goal. Lean will then repeatedly replace all left-hand-side occurrences in the current goal or specified hypotheses with the right-hand-side. If we want to perform a right-to-left rewrite for a certain rewrite hypotheses we can state it with a right-to-left arrow in front of the argument. In our example we could also perform a rewrite ```lean rewrite [← h]``` to replace $1$ in the goal leaving us with $1 + 0 = 1 + 0$.

This form of rewriting only helps us to replace terms that are equal in Lean's type theory. However, sometimes we want to represent mathematical structures in Lean that have their own notion of equivalence but are not considered as such by Lean.

Let us consider the example of an implementation of a mathematical set in lean that lets us examine and compare set members. We could start by reusing Lean's lists for our sets. Unlike sets, lists can have duplicate elements and the order of elements matters. If we want to reason about the equality of two sets $s_1$ and $s_2$ we could not simply check for equality as seen before. If $s_1$ has three elements $[1, 1, 2]$ and $s_2$ has only two elements $[2, 1]$ they would not be considered equal in Lean although they should represent two equal sets.

In order to compare $l_1$ and $l_2$ as actual sets we have to define a custom relation for their equality:

```lean
def setEq {α : Type} : List α → List α → Prop :=
  λ l1 l2 ⇒ ∀ x, x ∈ l1 ↔ x ∈ l2
```

This definition ensures that we now represent set equality correctly. We can even show that `setEq` is an equivalence relation by proving the properties identity, symmetry, and transitivity. We can continue and define a function to add elements `addElem` that appends an element to the underlying list of our set representation:

```lean
instance set_eq_equivalence {α : Type} : Equivalence (@setEq α) where
  refl := fun l1 x => Iff.rfl
  symm := by
    intro x y hxy a
    apply Iff.symm
    exact hxy a
  trans := by
    intro x y z hxy hyz a
    apply Iff.intro
    intro hx
    rewrite [hxy a, hyz a] at hx
    exact hx
    intro hz
    rewrite [← hyz a, ← hxy a] at hz
    exact hz

def addElem {α : Type} (x : α) (l : List α) : List α :=
  x :: l
```

Furthermore, we can show that addition of two equivalent sets preserves the equivalence. We also refer to this behaviour as morphism for `setEq`. The Lean proof for this is tedious however. The relation `setEq` is not the same as equality and can thus not be rewritten. This means we would have to proof that addition preserves the set equivalence for every element we may want to add. To solve a goal, for instance the implication $mono("setEq") [1, 1, 2] space [2, 1] -> mono("setEq") (mono("addElem" 3 space [1, 1, 2]) space (mono("addElem") 3 space [2, 1]))$. As we know that our addition of elements is a morphism for set equivalence, we would like to be able to rewrite just as we did with equality. To do this we need generalised rewriting.

Generalised rewriting is the ability to replace subterm $t$ with $u$ when they are related by an arbitrary relation $r$ @sozeau:inria-00628904. In Type Theorey, relations are defined as $alpha -> alpha -> mono("Prop")$ where $alpha$ can be an arbitrary type and `Prop` is the type of propositions. Equality ($=$) is of type $alpha -> alpha -> mono("Prop")$ in Lean and the biimplication ($<->$) is of type $mono("Prop") -> mono("Prop") -> mono("Prop")$. We will also refer to relation types of $alpha -> alpha -> mono("Prop")$ as $mono("relation") alpha$.

With generalised gewriting we could solve the above example by replacing the occurrence of $[1, 1, 2]$ in the proof goal by the right-hand-side of the rewrite theorem $[2, 1]$. A Lean proof where generalised rewriting is supported with a tactic `grewrite` would look like the following:

```lean
example : setEq [1,1,2] [2,1] → setEq (addElem 4 [1,1,2])  (addElem 4 [2,1]) := by
  intro h
  grewrite [h]
  rfl
```

Generalised rewriting can not only replace terms related by equivalence relations but also relations that are only transitive or only symmetric. This can be useful to replace terms in inequations. Consider the goal $a < c$ for instance and the two hypotheses $"haltb" : a < b$ and $"hbltc" : b < c$. With generalised rewriting we can replace the $a$ in the goal with $b$ by with a left-to-right rewrite ```lean rewrite [haltb]```. We can then close the goal using the other hypotheses.

The already present `rewrite` tactic for rewriting with equality and biimplication in Lean produces three outputs. The new goal after a rewrite occurred, a proof that the rewrite was just, and possible new subgoals that result from the rewrite. Theorem provers like Coq that already support generalised rewriting result in the same output information.

In this thesis, we will take a deeper look at the algorithm for generalised rewriting in type theory proposed by Mattheiu Sozeau @sozeau:inria-00628904, compare it to the actual implementation of generalised rewriting in Coq, extract the differences between the two, and show that those algorithms provide the same rewrite proofs. The algorithm described in the literature consists of two parts. The first part generates the rewritten term and proof of the rewrite including holes (or subgoals) that cannot be known when exploring a term. We also refer to this part of the algorithm as constraint generation algorithm as it leaves some open constraints. The second part of the algorithm solves those open subgoals (or constraints) using a proof search. Throughout this thesis we will pay more attention to the constraint generation and assert the generated proofs and constraints.

Our contributions to the research inlcude two implementations of generalised rewriting algorithms in Lean 4. The first one is a reimplementation of the literature version by Mattheiu Sozeau @sozeau:inria-00628904. The second implementation considers all improvements that have evolved in the Coq code base over the last two decades. Therefore, we provide the first description of the actual Coq rewriting algorithm including all those improvements. Our final contribution is an extension of the optimised Coq-inspired algorithm that makes the constraint generation more powerful than Coq's implementation and works for all cases described in the literature. This also includes a proof over the generated outputs of the algorithm. While our implementations generate the same proofs and constraints as the Coq's `rewrite` tactic does, our proof search is currently not as powerful as Coq's typeclass search. This may result in possible additional subgoals after performing certain rewrites.