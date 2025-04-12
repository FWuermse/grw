#import "./template.typ": *
#import "./theme.typ": *

= Equivalence of the Generated Rewrite Proofs

We saw that, in the typical case, the improved algorithm generates significantly fewer constraints and leads to more concise proofs. In the following, we want to show that the two proposed algorithms for constraint generation `Rew` and `ORew` provide the same rewrite proofs although with different constraints. The constraints still consist of metavariables of the types `relation`, `pointwiseRelation`, `Subrelation`, and `Proper` but in a more consise way.

#theorem()[When the algorithm $mono("Rew")_rho (t : tau)$ provides a proof for $?_r space t space u$ where $?_r$ is of type $mono("relation") space tau$ and $t != u$ for any given $tau$ and $rho$, then the modified algorithm $mono("ORew")_rho (t, ?_r)$ provides either *(1)* a proof for $?_r space t space u$ if the relation inference $?_r$ succeeds (see @updatedalgo) or *(2)* otherwise a proof of $?_r' space t space u$ where $?_r' : mono("relation" space tau)$ is a fresh metavariable of the same type $mono("relation") space tau$. If $t = u$, the $mono("ORew")$ algorithm with the same arguments returns just the flag `identity` whereas the $mono("Rew")$ algorithm provides a proof $p : ?_r space t space t$ *(3)*.] <theorem1>

#proof()[We proceed with structural induction over the term $t$. The cases for lambda, pi, and arrow only differ by the additional status field. It suffices to show that applying a proof of identity ($?_r space t space t$) is equivalent to leaving $t$ unchanged *(3)*. The application case can be proven by induction over the application subterms $e_0 space dots space e_n$. We start with the base case $n = 2$ (a function with one argument) and have to consider the three cases (identity, success), (success, identity), and (identity, identity) under the assumption that the case (success, success) is not possible for a binary well-formed Lean application. This is because for any $f space e$, the types $f : sigma_0 -> dots -> sigma_n -> tau$ and $e : sigma_0$ cannot be the same, thus cannot both unify. For simplicity we denote the left-hand side of the rewrite theorem $rho$ as $rho_"lhs"$ in the following cases:

- *$"Case binary application with " n = 2 space (e_0 space e_1)$*

  - *Case $e_0 space e_1$ with $rho : r space e_0 space u$*

    This is the base case for our induction over function application arguments where the function unifies and the only argument does not.

    *Proof Resulting from Rew:*\
    Given the outputs $r_e_0 : mono("relation") alpha -> tau$, $u : alpha -> tau$, and $p_e_0 : r_e_0 space e_0 space u$ of $mono("Rew")_rho (e_0)$ and the given outputs $r_e_1 : mono("relation") alpha$ and $p_e_1 : space r_e_1 space e_1 space e_1$ of $mono("Rew")_rho (e_1)$ the main invocation $mono("Rew"_rho) (e_0 space e_1)$ combines the proofs and carrier relations into a final proof of $r_tau (e_0 space e_1) space (u space e_1)$ where $r_tau$ is of type `relation` $tau$. We show the full Lean term including its type and all implicit arguments for all cases to highlight the well-formed composition of the proof terms:

    $#align(center + horizon)[
      #box(width: 80%, inset: 0pt)[
        $mono("Subrelation.subrelation") (alpha → tau) space r_e_0 space (r_e_1 ==> r_tau) \ (?_s : mono("Subrelation") space r_e_0 space (r_e_1 ==> r_tau)) space e₀ space u space p_e_0 space e₁ space e₁ space p_e_1 $
      ]
      #box(height: 40pt, width: 1%)[
        $ : r_tau space (e_0 space e_1) space (u space e_1)$
      ]
    ]$

    *Proof Resulting from ORew:*\
    Given $e_0 : alpha -> tau$ and $e_1 : alpha$ where $e_0$ unifies with the left hand side, we follow the case where we build pointwise relation constraints (See line 8 in @subterm) and obtain the following proof of $r_tau' (e_0 space e_1) space (u space e_1)$ from the `ORew` algorithm where $r_tau'$ is of type `relation` $tau$ and $r$ of type `relation` $alpha -> tau$:

    $#align(center + horizon)[
      #box(width: 84%)[
        $mono("Subrelation.subrelation") space (alpha → tau) space r space (mono("pointwiseRelation") space alpha space r_tau') \ space (?_s : mono("Subrelation") space r space (mono("pointwiseRelation") space alpha space r_tau')) space e₀ space u space h space e₁ $]
      #box(height: 30pt, width: 10%)[$: r_tau' space (e₀ space e₁) space (u space e₁)$]
      ]$

    Condition *(2)* holds because both cases result in the same proof (but possibly over a different relation) for $t != u$.

  - *Case $e_0 space e_1$ with $rho : r space e_1 space u$*

    When only the left-hand side of this minimal binary application unifies with $rho_"lhs"$:\
    *Proof Resulting from Rew:*\
    Given the outputs $r_e_0 : mono("relation") alpha -> tau$ and $p_e_0 : r_e_0 space e_0 space e_0$ of $mono("Rew")_rho (e_0)$ and the given outputs $r_e_1 : mono("relation") alpha$, $u : alpha$, and $p_e_1 : r_e_1 space e_1 space u$ of $mono("Rew")_rho (e_1)$ the `Rew` algorithm combines the proofs and carrier relations into a final proof of $r_tau : (e_0 space e_1) space (e_0 space u)$ where $r_tau$ is of type `relation` $tau$:

    $#align(center + horizon)[
      #box(width: 80%)[
        $mono("Subrelation.subrelation") (alpha → tau) space r_e_0 space (r_e_1 ⟹ r_tau) space \ (?_s : mono("Subrelation") r_e_0 space (r_e_1 ⟹ r_tau)) space e_0 space e_0 space p_e_0 space e_1 space u space p_e_1$
      ]
      #box(height: 30pt, width: 1%)[
        $: r_tau space (e_0 space e_1) space (e_0 space u)$
      ]
    ]$

    *Proof Resulting from ORew:*\

    With function argument unifying, we recursively invoke $mono("ORew"_rho) (e_0, r_tau : mono("relation") tau)$ and $mono("ORew"_rho) (e_1, r_tau)$. The first is flagged `identity` and thus returns no information. The latter results in a relation $r_e_1 : mono("relation") alpha$, and a proof $p_e_1 : r_e_1 space e_1 space u$. The algorithm then constructs a proof of $r_tau space (e_0 space e_1) space (e_0 space u)$:

    $#align(center + horizon)[
      #box(width: 80%)[
        $mono("Proper.proper") (alpha → tau) space (r_e_1 ⟹ r_tau) space e_0 space \ (?_p : mono("Proper") (r_e_1 ⟹ r_tau) space e_0) space e_1 space u space p_e_1$
      ]
      #box(width: 1%, height: 40pt)[
        $: r_tau (e_0 space e_1) space (e_0 space u)$
      ]]$

    The premise *(1)* holds because both cases result in the same proof for $t != u$.

  - *Case $e_0 space e_1$ where $rho$ does not unify given $rho : r space u space u'$*
    
    *Proof Resulting from Rew:*\

    Given the outputs $r_e_0 : mono("relation") alpha -> tau$ and $p_e_0 : r_e_0 space e_0 space e_0$ of $mono("Rew")_rho (e_0)$ and the given outputs $r_e_1 : mono("relation") alpha$ and $p_e_1 : space r_e_1 space e_1 space e_1$ of $mono("Rew")_rho (e_1)$, the `Rew` algorithm combines the proofs and carrier relations into a final proof of identity $r_tau (e_0 space e_1) space (e_0 space e_1)$ about the relation $r_tau$ of type `relation` $tau$:

    $#align(center + horizon)[
      #box(width: 80%)[
        $mono("Subrel.subrelation") (alpha → tau) space r_e_0 space (r_e_1 ⟹ r_tau) \ space (?_s : mono("Subrelation") r_e_0 (r_e_1 ⟹ r_tau)) space e_0 space e_0 space p_e_0 space e_1 space e_1 space p_e_1$
      ]
      #box(width: 1%, height: 40pt)[
        $: r_tau space (e_0 space e_1) space (e_0 space e_1)$
      ]
    ]$

    *Proof Resulting from ORew*:\
      `ORew` would simply return `identity` for such a rewrite exiting at line 40 in @subterm. As `Rew` returns proof of $r_tau space t space t$, this case also holds *(3)*.

- *Inductive case for $n + 1$ application subterms*

    We can now assume that we have a given application sequence where both algorithms produce the same rewrite proofs (carrier relation and holes may still differ). Our induction hypothesis states that:

    $(Psi', r, e_0 ' space dots space e_n ', p : r space (e_0 space dots space e_n) space (e_0' space dots space e_n')) := mono("Rew"_rho) (e_0 space dots space e_n)$ implies:\ $(Psi'', r',e_0 ' space dots space e_n ', p' : r' space (e_0 space dots e_n) space (e_0 ' space dots space e_n ')) := mono("ORew"_rho) (e_0 space dots space e_n, r)$ \ given that $e_0 space dots space e_n != e_0 ' space dots space e_n '$ and $(Psi'', mono("identity")) := mono("ORew"_rho) (e_0 space dots space e_n, r)$ otherwise.

    We must now also show that:\ $(Psi', r, e_0 ' space dots space e_(n+1) ', p : r space (e_0 space dots space e_(n+1)) space (e_0 ' space dots e_(n+1) ')) := mono("Rew"_rho) (e_0 space dots space e_(n+1) ')$ implies:\
    $(Psi'', r', e_0 ' space dots space e_(n+1) ', p' : r' space (e_0 space dots space e_(n+1)) space (e_0 ' space dots space e_(n+1) ')) := mono("ORew"_rho) (e_0 space dots space e_(n+1), r)$ \ if $e_0 space dots space e_(n+1) != e_0 ' space dots space e_(n+1) '$ and $(Psi'', mono("identity")) := mono("ORew"_rho) (e_0 space dots space e_(n+1), r)$ otherwise.

    There are four cases for the inductive step. Given the previous sequence was an identity rewrite, we must divide between another identity rewrite or a successful rewrite. If the previous sequence contains at least one successful rewrite, we also have the scenarios of another rewrite or a final identity. This differentiation is crucial to align with the optimisations for Leading Identity Rewrites and Status for Identity Rewrites.

  - *Case $e_0 space dots space e_n space e_(n+1)$ where we rewrote $e_0 space dots space e_n$ and $e_(n+1)$ unifies with $rho_"lhs"$*

    *Proof Resulting from Rew:*

    We can prove this similarly to the base case as we always treat applications as binary applications here and read left-to-right. We know from our induction hypothesis that we obtain a single relation, proof, and rewritten term from the rewrite on $e_1 space dots space e_n$. Let the relation be $r_e_n : mono("relation") (alpha_0 space dots space alpha_n space tau)$. As we only consider well-formed applications and we are considering the last element of such an application, we can imply that $r_e_n$ must be an arrow type. Let the recursively obtained proof be $p_e_n : r_e_n (e_0 ' space dots space e_n ') space (e_0 space dots space e_n)$, and thus $e_0 ' space dots space e_n '$ be the rewritten term. Similarly, the recursive invocation $mono("Rew")_rho (e_(n+1))$ outputs $r_e_(n+1) : mono("relation") alpha_(n+1)$, $u : alpha_(n+1)$, $p : r_e_(n+1) space e_(n+1) space u$. $r_tau$ is again the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$:

    $#align(center + horizon)[
      #box(width: 70%, inset: (top: 15%))[
        $mono("Subrelation.subrelation") space (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) \ space (?_s: mono("Subrelation") r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) \ space (e_0 ' space dots space e_n ') space p_e_n space e_(n+1) space u space p_e_(n+1)$
      ]
      #box(width: 30%, height: 45pt)[
        $: r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 ' space dots space e_n ' space e_(n+1) ')$
      ]
    ]$

    *Proof Resulting from ORew:*

    Knowing that unification of $e_(n+1)$ with the left-hand side of $rho$ implies that $e_0$ was not rewritten in this invocation and eliminates the possibility that the proof of the rewrite on $e_0 space dots space e_n$ consists of pointwise relation chains. Thus, we know that the current proof is a yet incomplete proper term including a respectful chain $mono("Proper.proper") (alpha_0 space dots space alpha_n space tau) space (?_r_0 ==> dots ==> ?_r_n ==> r_(alpha_n -> tau)) space e_0 space e_0 ' space p_e_0 space dots space e_n space e_n ' space p_e_n$ which has the type $r_(alpha_n -> tau) space (e_0 space dots space e_n) space (e_0 ' space dots space e_n ')$ where $r_(alpha_n -> tau) : mono("relation") space alpha_n -> tau$ is the desired output relation. The recursive call on $mono("ORew"_rho) (e_(n+1), )$ returns the carrier relation $r_e_(n+1) : mono("relation") alpha_(n+1)$, the updated term $e_(n+1) '$, and the proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1) '$. The algorithm then embeds the results into the current proof and returns a final proof of $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$ with $r_tau$ being of type `relation` $tau$:

    $#align(center + horizon)[
      #box(width: 60%, inset: (top: 15%))[
        $mono("Proper.proper") (alpha_0 -> dots -> alpha_n -> alpha_(n+1) -> tau) space \ (?_r_0 ==> dots ==> ?_r_n ==> r_e_(n+1) ==> r_tau) \ space e_0 space e_0 ' space p_e_0 space dots space e_n space e_n ' space p_e_n space e_(n+1) space e_(n+1) ' space p_e_(n+1)$
      ]
      #box(width: 35%, height: 53pt)[
        $: r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$
      ]
    ]$

    This case holds by our assumption *(1)* because the proofs are of equal types and $r_tau$ could be inferred by the `ORew` algorithm.

  - *Case $e_0 space dots space e_n space e_(n+1)$ we rewrote $e_0 space dots space e_n$ and $e_(n+1)$ does not unify with $rho_"lhs"$*

    *Proof Resulting from Rew*

    This case is similar to the previous one as `Rew` doesn't change depending on how the proof looks. Let the relation be $r_e_n : mono("relation") (alpha_0 space dots space alpha_n)$. Let the proof be $p_e_n : r_e_n (e_0 ' space dots space e_n ') space (e_0 space dots space e_n)$, and $e_0 ' space dots space e_n '$ the rewritten term. The recursive invocation $mono("Rew")_rho (e_(n+1))$ outputs $r_e_(n+1) : mono("relation") alpha_(n+1)$, $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$. $r_tau$ is again the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$:

    $#align(center + horizon)[
      #box(width: 70%, inset: (top: 15%))[
        $mono("Subrelation.subrelation") (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) \ space (?_s : mono("Subrelation") r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) space (e_0 ' space dots space e_n ') \ space p_e_n space e_(n+1) space e_(n+1) space p_e_(n+1)$
      ]
      #box(width: 30%, height: 46pt)[
        $: r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 ' space dots space e_n ' space e_(n+1))$
      ]
    ]$

    *Proof Resulting from ORew*

    When a previous rewrite occurred, we have to consider two sub-cases. Either the rewrite occurred on the very first argument $e_0$ and thus constructs a pointwise relation chain or some arguments of $e_1 space dots e_n$ were rewritten in which case we must consider a respectful chain.

    In the case of the successful rewrite on $e_1 space dots space e_n$, we obtain the desired proof $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space space e_1 ' space dots space e_n ' space e_(n+1))$ given the newly created carrier relation $r_e_(n+1) : mono("relation") space alpha_(n+1)$ and identity proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$. When combined like the following, the proofs of `ORew` and `Rew` are already of equal type, and the assumption *(1)* holds directly:

    $#align(center + horizon)[
      #box(width: 70%, inset: (top: 15%))[
        $mono("Proper.proper") (alpha_0 -> dots -> alpha_n -> tau) \ (?_r_0 ==> dots ==> ?_r_n ==> ?r_(n+1) ==> r_tau) \ space e_0 space (?_p : mono("Proper") (?_r_0 ==> dots ==> ?_r_n ==> ?r_(n+1) ==> r_tau) space e_0) \ space e_1 space e_1 ' space p_e_1 space dots space e_(n+1) space e_(n+1) ' space p_e_(n+1)$
      ]
      #box(width: 30%, height: 72pt)[
        $: r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 ' space dots space e_n ' space e_(n+1))$
      ]
    ]$

    In case of the successful rewrite on $e_0$, we obtain the desired (and per proof irrelevance equal) proof $r_tau ' space (e_0 space dots space e_(n+1)) space (e_0 ' space e_1 space dots space e_(n+1))$ given the newly created carrier relation $r_tau ' : mono("relation") space tau$ and the given $r_e_0$ of type `relation` $alpha_0 -> space dots space alpha_n -> tau$:

    $#align(center + horizon)[
      #box(width: 75%, inset: (top: 15%))[
        $mono("Subrelation.subrelation") space (alpha_0 space dots space alpha_(n + 1) space tau) \ space r_e_0 space (mono("pointwiseRelation") space alpha_0 (dots (mono("pointwiseRelation") space alpha_(n+1) space r_tau')dots) \ space (?_s : mono("Subrelation") space r_e_0 space (mono("pointwiseRelation") space alpha_0 (dots \ (mono("pointwiseRelation") alpha_(n+1) space r_tau')dots))) space e_0 space e_0 ' space p_e_0 space e_1 space dots space e_(n+1)$
      ]
      #box(width: 25%, height: 72pt)[
        $: r_tau' space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 ' space dots space e_n space e_(n+1))$
      ]
    ]$

    For completeness of this second case, we must consider deeply nested additional occurrences of $rho_"lhs"$ in this case, which would mean that while $e_1 space dots space e_(n+1)$ does not unify with $rho_"lhs"$ directly, it may unify deeper in the term tree. As shortly mentioned during @updatedalgo, we would rewrite the updated term $e_0 ' space e_1 space dots space e_(n+1)$ again in which case $e_0 '$ cannot be rewritten again (rewrite is an idempotent operation) which falls back to the first case where $e_1 space dots space e_n$ can be rewritten. We demand transitivity using a metavariable $?_T : mono("Transitive") space r_tau$ for $r_tau$ (obtained by inference from $r_tau '$) and thus obtain the final proof $p : r_tau space (e_0 space dots space e_n space dots e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$ which is equal to the type of the rewrite output by `Rew`.

    Both sub-cases hold by our assumption *(1)*.

  - *Case $e_0 space dots space e_n space e_(n+1)$ where $e_0 space dots space e_n$ was not rewritten and $e_(n+1)$ unifies with $rho_"lhs"$*

    *Proof resulting from Rew*

    Let the identity proof obtained by $mono("Rew")_rho (e_0 space dots space e_n)$ be $p_e_n : r_e_n space (e_0 space dots space e_n) space (e_0 space dots space e_n)$. The recursive invocation $mono("Rew")_rho (e_(n+1))$ outputs the relation $r_e_(n+1) : mono("relation") alpha_(n+1)$, the updated term $e_(n+1) '$, and the proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1) '$. $r_tau$ is the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1) ')$:

    $#align(center + horizon)[
      #box(width: 80%, inset: (top: 15%))[
        $mono("Subrelation.subrelation") (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) \ (?_s : mono("Subrelation") r_e_n space (r_tau ==> r_e_(n+1))) \ (e_0 space dots space e_n) space (e_0 space dots space e_n ) space p_e_n space e_(n+1) space e_(n+1) ' space p_e_(n+1)$
      ]
      #box(width: 20%, height: 50pt)[
        $ : r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 space dots space e_n space e_(n+1) ')$
      ]
    ]$

    *Proof Resulting from ORew*

    The subterm algorithm ignores arguments up until they can be rewritten. Thus, the application $e_0 space dots space e_n$ remains unchanged, and we build the Proper constraint based of the relation $r$, the new term $e_(n+1) '$, and the proof $p : r space e_(n+1) space e_(n+1) '$ and curry all unchanged arguments $e_0 space dots space e_n$. The algorithm results in a proof for $r_tau e_0 space dots space e_(n+1) space e_0 space dots space e_(n+1) '$ with $r_tau$ of type `relation` $tau$:

    $#align(center + horizon)[
      #box(width: 60%, inset: (top: 35%))[
        $mono("Proper.proper") (alpha -> tau) space (r ⟹ r_tau) space (e_0 space dots space e_n) \ (mono("Proper") (r ⟹ r_tau) space (e_0 space dots space e_n)) space e_(n+1) space e_(n+1) ' space p$
      ]
      #box(width: 40%, height: 25pt)[
        $: r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 space dots space e_n space e_(n+1) ')$
      ]
    ]$

    The premise *(1)* holds because both cases result in the same proof for $t != u$.

  - *Case $e_0 space dots space e_n space e_(n+1)$ was not rewritten $e_0 space dots space e_n$ and $e_(n+1)$ doesn't unify with $rho_"lhs"$*

    *Proof Resulting from Rew*

    Let the carrier $r_e_n : mono("relation") space alpha_n -> tau$ identity proof be $p_e_n : r_e_n (e_0 space dots space e_n) space (e_0 space dots space e_n)$. The recursive invocation $mono("Rew")_rho (e_(n+1))$ outputs the relation $r_e_(n+1) : mono("relation") alpha_0$ and the second identity proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$. $r_tau$ is the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1))$ with $r_tau$ of type `relation` $tau$:

    $#align(center + horizon)[
      #box(width: 80%, inset: (top: 15%))[
        $mono("Subrelation.subrelation") (alpha_(n+1) -> dots -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) space \ (?_s : mono("Subrelation") r_e_n space (r_tau ==> r_e_(n+1))) \ space (e_0 space dots space e_n) space (e_0 space dots space e_n) space p_e_n space e_(n+1) space e_(n+1) space p_e_(n+1)$
      ]
      #box(width: 20%, height: 50pt)[
        $ : r_tau space & (e_0 space dots space e_n space e_(n+1)) \ & (e_0 space dots space e_n space e_(n+1))$
      ]
    ]$

    *Proof Resulting from ORew*

    The subterm algorithm terminates at line 40 in @subterm and merely returns `identity` which holds under our assumption *(3)* because `Rew` algorithm provides a proof of $r_tau space t space t$ in this case.
    ]

    To show that both algorithms result in the same rewrite of propositions, we need to prove another theorem about the transition to implications.

    #theorem()[
      If $mono("InferRel") (mono("Rew")_rho (t : "Prop"), t)$ for $rho : r space t space u$ provides a proof of a rewrite from $t$ to $u$ of the form $t <- u$ containing metavariables, then the updated algorithm $mono("InferRel") (mono("ORew"_rho) (t, <-), t)$ also provides a proof of a rewrite from $t$ to $u$ of the form $t <- u$ containing metavariables.
    ] <theorem2>

    #proof()[To prove that both algorithms result in the same rewrite proof can be shown with the following case distinction inside `InferRel`:

- *Case `Rew` returns a proof for $r space t space u$ with $t != u$ and `ORew` infers $r$*

  In this case, the `InferRel` algorithm would match the `success` branch for both rewrite results (@theorem1) and return the `ORew` result, which was already inferred by the assumption of this case, directly providing a proof $t <- u$. The `Rew` algorithm outputs a metavariable of type `relation Prop` which is wrapped in the subrelation inference in line 8 at @infersubp. Both cases result in a proof for $t <- u$.

- *Case `Rew` returns a proof $r space t space u$ for $t != u$ and `ORew` cannot infer $r$*

  In this case, both results follow the same path in `InferRel`. Both exit at line 9 in @infersubp and provide a proof for $t <- u$.

- *Case `Rew` provides a proof for an identity rewrite*

  Using @theorem1 *(3)*, we can imply that `ORew` returns nothing (just an identity flag), and given $t = u$, the `impl_self` theorem creates a proof of $t <- t$ which is equal to the proof $p : r space t space t$ of `Rew` that is transformed to $t <- t$ in line 8 in @infersubp.
]

With the proofs for @theorem1 and @theorem2, we have shown that for all proofs generated by the `Rew` algorithm for a given term $t$, the `ORew` algorithm generates proofs of the same type and thus generates the same proofs. When looking at the proof terms, we can also observe that in every mentioned case the proof term and the constraints generated are of equal or smaller size in the `ORew` algorithm. This assures us that even in the worst-case scenario we are guaranteed proofs with no more (even if not significantly less) constraints.