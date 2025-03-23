= Related Work

There has been two major approaches in the Lean community to implement generalised rewriting. The first one is a yet open pull request on the Github repository for Lean's mathematics library @mathlib. This implementation provides a tractic that focuses on solving inequality rewrites only and thus is not a geneal rewriting algorithm. This approach is mostly based on the automated application of theorems about transitivity of relations.

Another approach for generalised rewriting that was developed by Sébastien Michelland implements the most crucial rules of the `Rew` algorithm that we mentioned in @PaperAlgo. This implementation stands out by its custom proof search tactic that mimics Coq's eauto tactic @eauto leveraging a custom extensible hint database. This proof search is tailored to the constraints resulting from the `Rew` algorithm which may differ from the constraints `Subterm` produces. While this proof search performed well as a drop-in-replacement for our use of aesop when solving constraints produced by the `Rew` algorithm it was not sufficient to solve the constraints generated by our `Subterm` algorithm only using theorems (not tactics) as hints.

Finally, we want to give a brief overview over the history of rewriting in Coq and demonstrate the value of having extracted the core essence of that in a compact format. Traversing and understanding the two decades of changes, splits, and unions of the code base was essential for this thesis.

The Coq theorem prover has supported propositional equality rewriting almost since it was created. However, this tactic (or core feature) was limited to equality only. By 2005 Coq received support for generalised rewriting of asymmetric relations with the `setoid_replace` module of the `reflexive` tactic. Later `setoid_replace` was moved to `class_tactics` and finally moved `setoid_rewrite` and bacame its own module.

Around the time of the release of the paper "A New Look at Generalized Rewriting in Type Theory" @sozeau:inria-00628904 tactics for automated proof search such as `autorewrite` and `eauto` got more entangled with the `setoid_rewrite` tactic and support for equality-, symmetric-, transitive-relations was added. This is also when the generalised rewriting approach became the default rewrite tactic and the leibniz-equality was used as a fall-back whenever the relation was equality. Around 2010 all the above tactics were merged and support for rewriting behind binders was added. This merge included heavy references to the module for definitional equality, Coq's typeclass search, and the definitions for morphisms and signatures. All contributors made an effort to keep all functionality backwards compatible which made the merge more verbose. Since 2010 many miscellaneous API and naming changes dominated the codebase of what is now one large tactic in `rewrite.ml`.