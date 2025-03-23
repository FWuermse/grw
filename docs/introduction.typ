#import "./template.typ": *
#import "./theme.typ": *

= Introduction <Introduction>
TODO: Fix up proof (use mono font).
TODO: Cover ResultType in section 4.
TODO: mention why we even need rewrite proofs (we're extending Lean and not changing it's core theory and defeq stuff.)

Rewriting in theorem provers is the process of replacing a subterm of an expression with another term. When and if such a rewrite can happen depends on the context, i.e., the information we have about the two terms. In Lean, rewriting is possible when two terms $t$ and $u$ are equal $t = u$ or with respect to the `propext` axiom when two propositions $p : mono("Prop")$ and $q : mono("Prop")$ imply each other $p <-> q$. This allows us to replace a term in a goal we want to solve or inside one of our hypothesis when reasoning in Lean.

This allows us to proof mathematical propositions such as the commutativity for multiplication. In the below example we can see a lean proof of the commutativity of multiplication given that addition is commutative:

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
theorem mul_comm (m n : ℕ) :
  mul m n = mul n m := by
  induction m with
  | zero => apply mul_zero
  | succ m' ih =>
    simp [mul]
    rewrite [mul_succ]
    rewrite [add_comm]
    rewrite [ih]
    rfl
```

In this example we want to proof that for any natural numbers $n$ and $m$ the multiplication $n dot m$ is equal to $m dot n$. In Lean, we do this using structural induction #footnote[Structural induction means that the induction follows the structure of the inductive type.] on the inductive type $NN$ which consists only of two constructors, `zero` for constructing 0 and `succ` for constructing any successor number. After unfolding the `mul` definition in line 6 we are left with a goal: $("succ" m) dot n = n + (n dot m)$. The `mul_succ` theorem has the type $("succ" m) dot n = (m dot n) + n$. The theorems left-hand side matches the left hand side of the theorem and thus we can rewrite it (replacing the left-hand side of the goal with the right-hand side of our theorem). The resulting goal is $(m dot n) + n = n + (n dot m)$ which can be closed by another rewrite with an addition-commutativity theorem and finally the induction hypothesis ($m dot n = n dot m$) which also proves equality and can thus be used in a rewrite.

While this is sufficient considering the many helpful theorems and tactics Lean 4 offers, there are some cases @iris TODO where it would be helpful to consider more general rewrites that exceed equality and if and only if. When we try to solve a goal in a theorem prover we usually have a given set of hypothesis and can access theorems that we have already proven as well as tactics that can apply multiple theorems. When we want to rewrite a goal which contains a term $t$ that we want to change to a term $u$ we can perform a rewrite by simply showing that $u$ implies $t$, and thus it suffices to show $u$. The relation ($<->$) is convenient because it gives us such an implication per definition. However, it is possible to perform a rewrite using any relation that can lead to the desired implication.

In the Lean and Coq theorem provers relations on a type $alpha$ are defined by $alpha arrow alpha arrow mono("Prop")$. When we want to prove a goal $t : mono("Prop")$ and have the hypothesis of $u : mono("Prop")$ as well as a proof $h$ of $r space t space u$ given $r$ is a relation $mono("Prop") arrow mono("Prop") arrow mono("Prop")$, we can proof the statement given we have the additional information that $r$ implies ($<-$), essentially ($<-$) is a subrelation of $r$. When those hypotheses are in place the proof is straight forward for this minimal example. By Leans definition of subrelations it suffices to show $r space t space ?_t$ and $?_t$. The question marks refer to missing values that can be filled with any given term that matches its type (metavariables in Lean or existential variables in Coq). Metavariables are also used to represent goals in Lean. Metavariables of a certain type $tau$ in can be assigned with any value $Gamma tack e : tau$ in the current context $Gamma$ (hypotheses, theorems, etc.). When we assign a metavariable that represents a goal, we also close the goal. Another way to use metavariables is to use them as placeholders in any given Lean term when the value is unknown at the time of creation. It is also possible to share a metavariable $?_x$ across multiple terms as seen in this example. Assigning it with a value $v$ also assigns every occurrence of $?_x$ with $v$. We can thus assign $?_t$ with $u$ and use our hypothesis that proves $u$ to complete the proof of our simple rewrite.

This approach is tedious to be performed manually especially when the goal is more complicated or the term we intend to rewrite is bound by a lambda expressions or an all quantifier. When we want to prove a goal $p and q$ with the same context for instance, and we need to rewrite $p$ to $q$ inside the left-hand side of the conjunction (replace $p$ the  without modifying the remaining term), the proof of that rewrite requires us to set a new subgoal $p and q -> q and q$, solve that by the rule for conjunction introduction leaving $t$ and $u$ as sub-subgoals. $u$ can be proven by our hypothesis and the proof for $t$ is the same procedure as for the minimal rewrite example above. Even this approach is specific to conjunctions and can't be extended for other propositions.

A better approach for a general way of rewriting with arbitrary relations is by using the Morphism framework introduced by Mattheiu Sozeau @sozeau:inria-00628904 consisting of `respectful` and `Proper` definitions that can construct proofs for arbitrary terms using a syntax-directed algorithm. The `Proper` definition in @ProperDef merely takes a relation $r$ and an element $m$ in that relation demanding reflexivity of that element. Whenever this definition holds we call $m$ a `Proper` element of $r$ meaning that $m$ is a morphism for $r$. The `respectful` definition seen in @respectfulDef denoted as ($==>$) is Coqs notion for signatures. This definition can produce very general implications for a variety of functions. For instance, the contrapositive theorem $forall a b : mono("Prop"), (a -> b) -> (not b -> not a)$ can be stated as $((->) ==> (<-)) space (not) space (not)$. We can even simplify the contrapositive theorem by leveraging `Proper` and `respectful` with $"Proper" ((->) ==> (<-)) space (not)$. We can use the same framework to specify the above rewrite $p and q -> q and q$ in a more general way for instance when we create a term $?_p$ of type $"Proper" ((=) ==> (<->) ==> (<-)) space (and)$ translates to $forall x y, x = y -> forall x' y', x' <-> y' -> (x and x' <- y and y')$. When instantiating the variables in $?_p$ for instance with $p, q, h : p = q, q, q, (h' : b <-> b)$ we would obtain a proof for $(p and q <- q and q)$.

Note that for this case it does not matter whether we have ($<->$), ($->$), or ($=$) as the middle argument for the respectful chain. In fact, any reflexive relation over `Prop` would work here. Proceeding with this framework we have to be mindful of what problems we can simplify with `Proper` and `respectful` proofs. We also need to consider which relations we use inside such a chain, how to choose the first and final relation, and finally what element we want to be proper under the sequence of `respectful` relations.

#definition("Proper")[
  ```lean
  class Proper (r : relation α) (m : α) where
    proper : r m m
  ```
] <ProperDef>

#definition("respectful")[
  ```lean
  def respectful (r : relation α) (r' : relation β) : relation (α → β) :=
    λ f g ↦ ∀ x y, r x y → r' (f x) (g y)
  ```
] <respectfulDef>

The Coq library for morphisms has many theorems that operate on `Proper` and `respectful` terms which helps to construct and solve theorems containing morphisms and signatures. This allows us to use the same structure and theorems for rewrites in different terms. The proof construction for the rewrite proofs $p and q <- q and q$ and $p or q <- q or q$ can both be realised using `Proper` and `respectful`. This generalisation is the base for an algorithm proposed by Matthieu @sozeau:inria-00628904 that automatically produces rewrite proofs for any given `Proper` relation where the term to be rewritten can be behind binders and nested in other structures. There is one more definition that makes the proposed algorithm more powerful. When we have a term $mono("Proper") (A ==> B) space f$, and we know that $B$ is a subrelation of $C$ we can imply that $mono("Proper") (A ==> C) space f$ holds.

#definition("Subrelation")[
  ```lean
  class Subrelation (q r : α → α → Prop) :=
    subrelation : ∀ {x y}, q x y → r x y
  ```
]

In this thesis we will take a deeper look at the algorithm for generalised rewriting in type theory @sozeau:inria-00628904, compare it to the actual implementation of generalised rewriting in Coq, extract the differences between the two, and show that those algorithms provide the same rewrite proofs.

This highlights our contributions, wich are the following:
- Implement the algorithm seen in the paper in Lean 4
- Provide the first description of the optimised Coq implementation that evolved over the last decades
- Implement the optimized algorithm in Lean 4
- Complete the optimized algorithm to be consistent with the algorithm mentioned in the paper
- Show that both algorithms lead to the same rewrite proofs