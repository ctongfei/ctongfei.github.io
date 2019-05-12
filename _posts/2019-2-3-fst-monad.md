---
layout: post
title: Abstractions of FSTs with Monads
comments: true
---


Finite state machines (FSTs) are usually formulated as a tuple $$ (S, A, B, S^I, S^F, \delta) $$ comprising of the following components:
  - $$ S $$: The set of __states__;
  - $$ A $$: The __input__ alphabet;
  - $$ B $$: The __output__ alphabet;
  - $$ S^I \subseteq S $$: The set of initial states;
  - $$ S^F \subseteq S $$: The set of final states;
  - $$ \delta \subseteq (S \times A) \times (S \times B) $$: The transition relation.

We encode this in Scala:

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
  
  def compose[A, B, C](
                       t2: Transducer[B, C], 
                       t1: Transducer[A, B]
                      ): Transducer[A, C] =
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

However, the output encoding of the `next` function, `Set[(S, B)]` is not ideal: what if each output is assigned a weight (weighted FSTs)? What if the output given a specific state and input form a distribution (stochastic FSTs)? 

Note that the `next` function in `compose` is implemented elegantly through a _monadic_ comprehension. Let's abstract this __monad__ out:

```scala
trait Transducer[F[_], -A, +B] {
    type S
    def initialStates: F[S]
    def finalStates: F[S]
    def next(s: S, a: A): F[(S, B)]
}
```
We call this `F`-transducer: the `F` higher-kinded type encapsulates the __effect__ of moving the transducer state to another given an input! `F` could be 
  - `Id`: Deterministic FSTs;
  - `Option`: Determinstic FSTs with some edges lead to failure case;
  - `Set`: Non-deterministic FSTs;
  - `Stochastic`: Stochastic FSTs;
  - `Weighted`: Weighted FSTs.

Let's take the weighted case as an example, since weighted FSTs (WFSTs) are of utmost importance in a variety of domains, e.g. automatic speech recognition.

\\[
  W = \\{ (a, r) \\}; a \in A, r \in R
\\]
```scala
  type Weighted[A, R] = Map[A, R]
```

`Weighted` form a monad given a semiring $$(R, \mathbb{0}, \mathbb{1}, \oplus, \odot)$$ on the weight type `R` (this is how WFSTs work in speech recognition):
\\[
\begin{align}
  \textrm{pure}(a) &= \left\\{ (a, \mathbb{1}) \right\\} \\\\\\\\
  \textrm{map}(W, f) &= \left\\{ (f(a), r) \mid (a, r) \in W \right\\} \\\\\\\\
  \textrm{flatMap}(W, f) &= \left\\{ \left(b, \bigoplus_{(a,r)\in W} \bigoplus_{(b, r^\prime) \in f(a)} r \odot r^\prime \right) \middle| b \in B \right\\}
\end{align}
\\]
```scala
implicit def WeightedMonad(implicit R: Semiring[R]) 
  extends Monad[Weighted[_, R]] { 
    // let's pretend Scala has type lambda syntax here
  def pure[A](a: A) = Map((a, R.one))
  def map[A, B](wa: Map[A, R])(f: A => B) = 
    wa.map { case (a, r) => (f(a), r) }.toMap
  def flatMap[A, B](wa: Map[A, R])(f: A => Map[B, R]) = 
    (
      for {
        (a, r0) <- wa
        (b, r1) <- f(a)
      } yield (b, R.times(r0, r1))
    ).groupBy {
      case (b, r) => b
    }.mapValues(_.map(_._2).sum)
}
```
Hence we have the `Weighted`-Transducer, therefore we have a category over WFSTs. Essentially, we have the following implicit proving relations:
```hs
  Semiring[R] => Monad[Weighted[_, R]]
  Monad[F] => Category[Transducer[F, _, _]]
```
I think that this is really illuminating, as it shows the structure of FSTs through the lens of abstracted types.
