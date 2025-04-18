#pagebreak()
= Conclusion

As part of this thesis, we have implemented the algorithm for generalised rewriting proposed by Matthieu Sozeau @sozeau:inria-00628904 and identified some critical performance issues with the literature version. We extracted and presented the essence of the historically grown mixture of algorithms that is used in the majority of Coq proofs. We extended the algorithm to be as powerful as the version we have seen in the literature while still keeping the enumerated benefits. Lastly, we have shown that both algorithms produce the same proofs despite having evidently less metavariables to be solved in the proof search that grows exponentially depending on the amount of metavariables. Finally, we have implemented the improved algorithm in Lean 4.

Our custom extensible proof search does not find assignments for all constraints Coq's typeclass search can solve. This is because we have not translated the remaining hundred tactics mentioned in Coq's Morphism library @coqmorphism to Lean 4. We leave that translation as future work to make our rewrite tactic as powerful as Coq's.

#show heading.where(level: 1): set heading(numbering: none)

= Acknowledgments

I thank Jannis Limperg for his supervision and useful support with Lean 4 metaprogramming and assistance with making the automated proof search extensible. Furthermore I want to thank Matthieu Sozeau for his helpful comments about Coq's rewriting implementation on the Coq Zulip chat.