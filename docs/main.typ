#import "./template.typ": *
#import "./theme.typ": *
#import "@preview/dashy-todo:0.0.1": todo
#import "@preview/glossarium:0.5.1": make-glossary, register-glossary, print-glossary, gls, glspl
#import "@preview/algo:0.3.4": algo, i, d, comment, code

= Introduction <Introduction>

Rewriting in theorem provers is the process of replacing a subterm of an expression with another term. When and if such a rewrite can happen depends on the context, i.e. the information we have about the two terms. In Lean, rewriting is possible when two terms `t` and `u` are equal ```lean t = u``` or with respect to the `propext` axiom when two propositions `p : Prop` and `q : Prop` imply each other ```lean p <-> q```. This allows us to replace a term in a goal we want to solve or inside one of our hypothesis when doing reasoning in Lean.

This allows us to proof mathematical propositions such as the commutativity for multiplication. In the below example we can see a lean proof of the commutativity of multiplication given that additon is commutative:

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

In this example we want to proof that for any natural numbers $n$ and $m$ the multiplication $n dot m$ is equal to $m dot n$. In Lean we do this using structural induction #footnote[Structural induction means that the induction follows the structure of the inductive type.] on the inductive type $NN$ which consists only of two constructors, `zero` for constructing 0 and `succ` for constructing any successor number. After unfolding the `mul` definition in line 6 we are left with a goal $("succ" m) dot n = n + (n dot m)$. The `mul_succ` theorem has the type $("succ" m) dot n = (m dot n) + n$. The theorems left hand side matches the left hand side of the theorem and thus we can rewrite it (replacing the left hand side of the goal with the right hand side of our theorem). The resulting goal is $(m dot n) + n = n + (n dot m)$ which can be closed by another rewrite with an addition commutativity theorem and finally the induction hypothesis ($m dot n = n dot m$) which also proves equality and can thus be used in a rewrite.

While this is sufficient considering the many helpful theorems and tactics Lean 4 offers, there are some cases @iris TODO where it would be helpful to consider more general rewrites that exceed equality and if and only if. When we try to solve a goal in a theorem prover we usually have a given set of hypothesis and can access theorems that we've already proven as well as tactics that can apply multiple theorems. When we want to rewrite a goal which contains a term `t` that we want to change to a term `u` we can perform a rewrite by simply showing that `u` implies `t` and thus it suffices to show `u`. The relation ($<->$) is convenient because it gives us such an implication per definition. However it is possible to perform a rewrite using any relation that can lead to the desired implication.

In the Lean and Coq theorem provers relations on a type $alpha$ are defined by $alpha arrow alpha arrow "Prop"$. When we want to proove a goal `t : Prop` and have the hypothesis of `u : Prop` as well as a proof of `h : r t u` given `r` is a relation $"Prop" arrow "Prop" arrow "Prop"$ we can proof the statement given we have the additional information that `r` implies ($<-$), essentially ($<-$) is a subrelation of `r`. When those hypothesis are in place the proof is straight forward for this minimal example. By Leans definition of Subrelations it suffices to whow `r t ?t` and `?t`. The question marks refer to missing values that can be filled with any given term that matches its type (Meta variables in Lean or existential variables in Coq). The second step is to instanciate `?t` with `u` and use our hypothesis that proves `u`.

This approach is tedious to be performed manually especially when the goal is more complicated or the term we intend to rewrite is bound by lamnda expressions or an all quantifier. When we want to prove a goal `p ∧ q` with the same context for instance and we need to rewrite `p` to `q` inside the lefthand side of the conjunction (replace `p` the  without modifying the remaining term), the proof of that rewrite requires us to set a new subgoal `p ∧ q → q ∧ q`, solve that by the conjunction introduction rule leaving `t` and `u` as sub-subgoals. `u` can be proven by our hypothesis and the proof for `t` is the same proceedure as for the minimal rewrite example above. Even this approach is specific to conjunctions and can't be extended for other propositions.

A better approach for a general way of rewriting with arbitrary relations is the Morphism framework introduced by Mattheiu Sozeau @sozeau:inria-00628904 consisting of `respectful` and `Proper` definitions that can construct proofs for arbitrary terms using a syntax-directed algorithm. The `Proper` definition in @ProperDef merely takes a relation $r$ and an element $m$ in that relation demanding reflexivity. Whenever this definition holds we call $m$ a `Proper` element of $r$ meaning that $m$ is a morphism for $r$. The `respectful` definition seen in @respectfulDef denoted as ($==>$) is Coqs notion for signatures. This definition can produce very general implications for a variaty of functions. For instance, the contrapositive theorem $forall a b : "Prop", (a -> b) -> (not b -> not a)$ can be stated as $((->) ==> (<-)) (not) (not)$. We can even simplify the contrapsitive theorem by leveraging `Proper` and `respectful` with $"Proper" ((->) ==> (<-)) (not)$. We can use the same framework to specify the above rewrite $p and q -> q and q$ in a more general way for instance when we create a term $p$ of type $"Proper" ((=) ==> (<->) ==> (<-)) " " (and)$ translates to $forall x y, x = y -> forall x' y', x' <-> y' -> (x and x' <- y and y')$. When instanciating the variables in $p$ for instance with $p, q, h : p = q, q, q, ("by rfl")$ we would get a proof for $(p and q <- q and q)$.

#definition("Proper")[
  ```lean
  class ProperProxy (r : relation α) (m : α) where
    proxy : r m m
  ```
] <ProperDef>

#definition("respectful")[
  ```lean
  def respectful (r : relation α) (r' : relation β) : relation (α → β) :=
    λ f g ↦ ∀ x y, r x y → r' (f x) (g y)
  ```
] <respectfulDef>

The Coq library for morphisms has many theorems that operate on `Proper` and `respectful` terms which helps to construct and solve theorems containing morphisms and signatures. This allows us to use the same structrue and theorems for rewrites in different terms. The proof construction for $p and q <- q and q$ and $p or q <- q or q$. This generalisation is the base for an algorithm proposed by Matthieu @sozeau:inria-00628904 that automatically produces rewrite proofs for any given `Proper` relation where the term to be rewritten can be behind binders and nested in other structures. There is one more definition that makes the proposed algorithm more powerful. When we have $"Proper" (A ==> B) " " f$ and we know that $B$ is a subrelation of $C$ we can imply $"Proper" (A ==> C) " " f$.

#definition("Subrelation")[
  ```lean
  def Subrelation (q r : α → α → Prop) :=
    ∀ {x y}, q x y → r x y
  ```
]

= Algorithm for Genralised Rewriting <PaperAlgo>

The algorithm in TODO:algoref is an imperative translation of the declarative algorithm proposed in @sozeau:inria-00628904 that we implemented in Lean 4. The algorithm is syntax directed and covers every term that can be constructed in Lean. The algorithm takes an empty constraint set $Psi$, a term $t$ in that we want to rewrite and a constant proof $rho$ that is of the type $r a b$ where $r$ is a relation, $a$ is a term we want to rewrite in $t$ and $b$ is the value we want to replace $a$ with. The algorithm outputs a modified set $Psi$ which contains all wholes in the rewrite proof that can't be determined in some of the cases of the algorithm (represented in meta variables in Lean), a carrier relation $r$ for the rewrite, the modified term $u$ and finally the proof for the rewrite. At the beginning we always check whether the term we want to rewrite unifies directly for the given proof $rho$. In that case the proof-result for a rewrite would just be $rho$. Because $rho$ (and any proof-result of this algorithm) is not of the type $t <- u$ we will wrap the output of the algorithm in a proof for $"Subrelation" r " " (<-)$.

Whenever the term does not unify directly we examine the structure and use a different approach depending on whether $t$ is an application, lambda, dependent/non-dependent arrow, or constant. Whenever we encounter an application $f e$ we perform a recursive call on both $f$ and $e$. We use the obtained carrier relation, proof, and term to construct a proof that $r_f$ is a subrelation of $r_e ==> ?_T$. This is where the first holes occur that we collect in the constraint set. This generates a proof for $r t u$. Recall that we construct a $"Subrelation" r " " (<-)$ after invoking `Rew` which leads to a proof of $t <- u$.

For rewrites inside lambda terms we bind $x : tau$ to the local context and perform a recursive rewrite on the body of the lambda. The resulting proof wrapped in a fresh lambda expression binding $x : tau$ represents the proof for $r " " (lambda x:tau. b) " " (lambda x:tau. b')$ again progressing to $(lambda x:tau. b) <- (lambda x:tau. b')$ eventually.

All other cases leverage either the lambda or application cases by converting them slightly to fit in the scheme. The non-dependent arrow case is just transformed into a function that represents an arrow. This has the advantage that locally declared functions (`impl` in this case) are considered const in Lean and thus just reuse the already defined application case. Similarly for the case of an all quantifier that uses a local dependent function `all`.

Finally we will take a look the last case is triggered whenever none of the above cases match. This is the case for constants such as `all`, `impl`, or simply for atoms that don't unify at the beginning of the `Rew` function. In this case we construct another meta variable of type $"Proper" tau " " ?_r t'$ that is treated as a hole at the bottom of the proof tree and essentially represents and identity rewrite from $t$ to $t$.

#algo(
  keywords: ("if", "else", "then", "match", "return", "with", "type"),
  title: $"Rew"_rho$,
  parameters: ($Psi$, $t$)
)[
  ($Psi'$, $r'$, $u'$, unifyable) := $"unify"_rho$($Psi$, $t$)\
  if unifyable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with#i\
  $|$ $f$ $e$ $=>$#i\
    ($Psi'$, $r_f$, $u_f$, $p_f$) := #smallcaps($"Rew"_rho$)$(Psi, f)$\
    ($Psi''$, $r_e$, $u_e$, $p_e$) := #smallcaps($"Rew"_rho$)$(Psi', e)$\
    $Psi'''$ := {$?_T$ : relation type(e), $?_"sub"$ : subrelation $r_f (r_e ==> ?_T)$}\
    return ($Psi'' union Psi'''$, $?_T$, $"app" u_f u_e$, $?_"sub" f u_f p_f e u_e p_e$)#d\
  $|$ $lambda$ x : $tau$. b $=>$#i\
    ($Psi'$, $r$, $u$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, b)$\
    return ($Psi'$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
  $|$ $forall x : tau, b$ $=>$#i\
    ($Psi'$, $r$, $u$, unifyable) := $"unify*"_rho$($Psi$, $b$)\
    if unifyable then:#i\
      return ($Psi'$, $r$, $u$, $rho$)#d\
    ($Psi'$, $r'$, $"all" (lambda x : tau. b')$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "all" (lambda x : tau. b))$\
    return ($Psi'$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
  $|$ $sigma -> tau$ $=>$#i\
    ($Psi'$, $r$, $"impl" sigma' " " tau'$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "impl" sigma " " tau)$\
    return ($Psi'$, $r$, $sigma' -> tau'$, $p$)#d\
  $|$ t' $=>$#i\
    return ($Psi union {?_r : $ relation type($t$), $?_m : "Proper" tau " "?_r " " t'}$, $?_r$, $t'$, $?_m$)
] <algo>

== Optimisations

#algo(
  keywords: ("if", "else", "then", "match", "return", "with", "type", "for", "in", "do"),
  title: $"Subterm"_rho$,
  parameters: ($Psi$, $t$)
)[
  ($Psi'$, $r'$, $u'$, unifyable) := $"unify"_rho$($Psi$, $t$)\
  if unifyable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with#i\
  $|$ $e_0 dots e_n$ $=>$#i\
    respectful := {}\
    prefixIsId := true\
    fn, u := $e_0$\
    for $e : tau$ in $e_0 dots e_n$ do#i\
      $(Psi, "result")$ := $"Subterm"_rho$$(Psi, e)$\
      if prefixIsId then#i\
        if $"result" = "identity"$#i\
          fn := fn e\
          u := u e\
          continue#d\
        else#i\
          prefixIsId := false#d#d\
    match result with#i\
    $|$ identity $=>$#i\
      $Psi$ := $Psi union {?_r : "relation" tau, ?_p : "ProperProxy" tau ?_r t}$\
      respectful := respectful ++ ${?_r}$\
      u := u e#d\
    $|$ success $=>$#i\

    #d\
    return ($Psi'' union Psi'''$, $?_T$, $"app" u_f u_e$, $f u_f p_f e u_e p_e$)#d\
  $|$ $lambda$ x : $tau$. b $=>$#i\
    ($Psi'$, $r$, $u$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, b)$\
    return ($Psi'$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
  $|$ $forall x : tau, b$ $=>$#i\
    ($Psi'$, $r$, $u$, unifyable) := $"unify*"_rho$($Psi$, $b$)\
    if unifyable then:#i\
      return ($Psi'$, $r$, $u$, $rho$)#d\
    ($Psi'$, $r'$, $"all" (lambda x : tau. b')$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "all" (lambda x : tau. b))$\
    return ($Psi'$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
  $|$ $sigma -> tau$ $=>$#i\
    ($Psi'$, $r$, $"impl" sigma' " " tau'$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "impl" sigma " " tau)$\
    return ($Psi'$, $r$, $sigma' -> tau'$, $p$)#d\
  $|$ t' $=>$#i\
    return ($Psi union {?_r : $ relation type($t$), $?_m : "Proper" tau " "?_r " " t'}$, $?_r$, $t'$, $?_m$)
] <algo>

== Updated Algorithm



== Equality of the Generated Proofs

#pagebreak()

= Related Work

= Conclusion

#pagebreak()

#bibliography("refs.bib", full: true, title: "References")
