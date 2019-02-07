---
layout: post
title: Abstractions of FSTs with Monads
---


Finite state machines (FSTs) are usually formulated as a tuple $$ (S, A, B, s_0, S_F, \delta) $$ comprising of the following components:
  - $$ S $$: The set of __states__;
  - $$ A $$: The __input__ alphabet;
  - $$ B $$: The __output__ alphabet;
  - $$ S^I \subseteq S $$: The set of initial states;
  - $$ S^F \subseteq S $$: The set of final states;
  - $$ \delta \subseteq (S \times A) \times (S \times B) $$: The transition relation.

We translate this to Scala:

```scala
trait Transducer[-A, +B] {
  type S
  def initialStates: Set[S]
  def finalStates: Set[S]
  def next(s: S, a: A): Set[(S, B)]
}
```
Here we encode the state type as an _existential_ type: they are internal and of no interest to the users of FSTs. Note that the output of the `next` function is a `Set[(S, B)]`: it encodes multiple possible transition outcomes given a state $$ s \in S $$ and input $$ a \in A $$.


One of the most interesting computational aspects of FSTs is that they can be _composed_ (unlike RNNs). Mathematically, given FST $$ T_1 = (S_1, A, B, S_1^I, S_1^F, \delta_1 ) $$ and $$ T_2 = (S_2, B, C, S_2^I, S_2^F, \delta_2) $$, we can compose these two into one FST $$ T_2 \circ T_1 $$, where strings $$ a \in A^*, c \in C^* $$ is accepted only if there exists $$ b \in B^* $$ such that $$ a[T_1]b \wedge b[T_2]c $$.

From a functional programming perspective, FSTs form a category here! 

```scala
implicit object TransducerCategory extends Category[Transducer] {
  def id[A]: Transducer[Id, Id] = 
    new Transducer[Id, Id] {
      type S = Unit
      def initialStates = Set(())
      def finalStates = Set(())
      def next(s: S, a: A): Set((s, a))
  }
  def compose[A, B, C](t2: Transducer[B, C], t1: Transducer[A, B]):Transducer[A, C] =
    new Transducer[A, C] {
      type S = (t1.S, t2.S)
      def initialStates = for {
        s1 <- t1.initialStates
        s2 <- t2.initialStates
      } yield (s1, s2)
      def finalStates = for {
        s1 <- t1.finalStates
        s2 <- t2.finalStates
      } yield (s1, s2)
      def next(s: S, a: A): (S, C) = {
        val (s1, s2) = s
        for {
          (s1_, b) <- t1.next(s1, a)
          (s2_, c) <- t2.next(s2, b)
        } yield ((s1_, s2_), c)
      }
    }
}
```

The `Set[(S, B)]` encoding is not ideal: what if each output is assigned a weight (weighted FSTs)? What if the output given a specific state and input form a distribution (stochastic FSTs)? It turns out that we can encode this elegantly with __monads__:

```scala
trait Transducer[F[_], -A, +B] {
    type S
    def initialStates: F[S]
    def finalStates: F[S]
    def next(s: S, a: A): F[(S, B)]
}
```
The `F[_]` higher-kinded type encapsulates the _effect_ of moving the transducer state to another given an input! `F[_]` could be 
  - `Id`: Deterministic FSTs;
  - `Set`: Non-deterministic FSTs;
  - `Stochastic`: Stochastic FSTs;
  - `Weighted`: Weighted FSTs.

We'll see later how should the `Weighted` monad be formed. 
