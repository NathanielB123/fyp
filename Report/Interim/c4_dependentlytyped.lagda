\chapter{Type Theory with Equational Assumptions}

Unlike with the simply typed case, we will delay the settling on concrete syntax
until we have examined several examples. One might find the lack of pinning down
a concrete formal definition of our syntax, conversion, reduction etc...
off-putting and if so, they are encouraged to to skip ahead to section (??).
The trouble is that defining a convenient \remarknote{exactly what I mean by
"convenient" will be explained in said section, but, in short, I would like to
avoid an untyped definition of syntax} syntax for dependent types is
significantly more troublesome.

Still no definition of syntax at all is probably extremely unhelpful, so instead
I present the following typing rules:

...

This definition is incomplete! We haven't defined substitutions (though one
could imagine them as working very similarly to substitutions in STLC) and more
critically, we haven't addressed how to cope with conversion (definitional
equality). Specifically, given terms are now capable of appearing in terms
(see Bool-elim-large) typing rules like application need to require a more
general equality of the domain and argument type than on-the-nose syntactic
equality.

\section{Special Cases}

\subsection{Closed Value Rewrites}

\subsection{Neutral Rewrites}

Neutrals have a nice property: they always block computation. 
This means normal forms are stable under neutral rewrites, and so if we are
able to decide equivalence under a set of neutral equations, this trivially
extends to deciding equivalence modulo the equations extended with beta.

Deciding equality modulo a set of ground equations can be done via ground
completion: ...

\subsection{Constructor-headed Rewrites}

We define constructor-headed rewrites as those of the form

\begin{code}
tⁿᵉ ↦ c u₁ ... u₁
\end{code}

where c is a constructor. These are arguably a strict generalisation of closed
value rewrites (section [?]). Unfortunately, the monotonicity of substitution
condition is no longer obviously provable, but neither can we freely (re)orient 
the rules to follow an encompassment ordering: if we rewrite from a term headed
by a constructor, we risk breaking confluence.

...

Luckily, dependent types show us an alternative. We can encode coproducts with
booleans and sigma types. 

CITE KENJI MAILLARD
...

We have developed a procedure to break rewrites of the form 

\begin{code}
tⁿᵉ ↦ inᵢ u₁ ... u₁
\end{code}

into a combination of closed value and neutral rewrites.

The occurs check

\subsection{Infinitary Types}

We have shown that equations between terms of first-order finitary types can be 
decomposed into more primitive building blocks, but we might hope to extend this
also to infinitary types, such as natural numbers, lists, trees
etc...

Eliminators for these types express their recursion/induction principles. To
destruct arbitrarily nested structures with a single invocation of the
eliminator, recursive occurences of the type in constructors are replaced with
the motive type.

% Formal definition of ℕ-rec
\begin{code}
-- In STLC, we can type the recursion principle for ℕs as
ℕ-rec : Tm Γ A → Tm (Γ , A) A → Tm Γ ℕ → Tm Γ A

-- In dependently typed lambda calculus, we can define the induction principle
ℕ-ind : (P : Ty (Γ , ℕ)) → Tm Γ (P [ < zero > ]) → Tm Γ ℕ
\end{code}


Arguably, the flat case constructs we have examined so far are
also recursors/induction principles, only the structure of the types in those
cases wasn't actually recursive, but there are important implications w.r.t.
smart case.


Induction poses some slight difficulties though. First of all, while induction
principles look a lot like the flat case constructs used to eliminate coproducts
their meaning is somewhat different. When inducting on natural numbers, we will
always eventually hit the base (zero) case irrespective of the input, so we
cannot soundly assume 'scrutinee = zero', even propositionally.

<COUNTER EXAMPLE HERE>

One could argue that in the 'suc'cessor case, we know the input natural number
must start with 'suc', but this is heavily reliant on the rest of the datatype.
If we instead inducted on a type of unnormalised integers:

\begin{code}
data ℤ : Set where
  su : ℤ → ℤ
  pr : ℤ → ℤ
  ze : ℤ
\end{code}

In the successor/predecessor cases, we can infer that the scrutinee must start 
with 'su' or 'pr' (i.e. it is definitely not 'ze') but that is not enough to
give us a unique value to rewrite to.

I therefore argue it is somewhat meaningless to try and integerate these 
equational assumptions with general inductive principles. However, sometimes
users may not wish to induct on an inductive type but merely do a case split,
splitting on a finite number of choices.

\begin{code}
is-zero : ℕ → Bool
is-zero ze     = true
is-zero (su _) = false
\end{code}

Elaborating such situations into pattern matches with coproducts is not too
tricky. Taking the view of inductive datatypes as fixpoints of strictly 
positive functors - the "initial algebra" - gives us 'fix : F (Fix F) → Fix F' 
and 'unfix : Fix F → F (Fix F)'. The initial algebra of 'ℕ' is 'λ X → 1 + X',
so we have
\begin{code}
unfix-ℕ : ℕ → ⊤ + ℕ
unfix-ℕ ze     = inl tt
unfix-ℕ (su n) = inr n
\end{code}

And now we can reuse our approach for dealing with coproducts (every
case split on a natural number 't' can be elaborated into a case split on
the coproduct 'unfix t'). 

There is perhaps one obvious limitation here: while repeated case splits on the
same natural number will reduce through iterated rewriting, any rewrite rule
'unfix t → u' will never fire on 't' itself. Consider

\begin{code}
case t of
  ze → let foo : t ≡ ze
           foo = refl
        in ...
  su _ → ...
\end{code} 

\begin{code}
case t of
  ze   → ℕ-elim t ?0 ?1
  su n → ?2
\end{code}

We can fix both of these problems by building 'fix'/'unfix' into the syntax 
more deeply and not including raw neutrals of type 'ℕ' in normal forms.

Instead, we add the rule

Γ ⊢ⁿᵉ t : ⊤ + ℕ
---------------
Γ ⊢ⁿᶠ fix t : ℕ

Now neutrals 'tⁿᵉ : A' reduce to 'fix (unfix tⁿᵉ) : A', and rewrites targetting
'unfix tⁿᵉ' can fire.

Inductive types bring up one final concern: what if an equation is recursive?
For example 't = su t'. I consider cases:
- Raw 't = su t' equations: we can label the current match branch as impossible.
  Note Agda already rejects cyclic equations involving variables: we merely
  need to extend this to neutral terms by running a conversion check between the
  LHS and each argument to the constructor on the RHS.
- 't = su (f t)' where 'f t' is a neutral blocked on 'f'. These cases can
  be decomposed
- 't = su (f t)' where 'f t' is a neutral blocked on 't'. Now we are in trouble.
  TODO: This isn't really possible in the sense that 'f' cannot be a function
  here. It has to be an eliminator of some form.

\section{Categories with Families}




This should be obvious - but if we use a quotiented syntax, that means we have
to go reduction-free (citation needed - I'm not actually convinced this is true
lol)


\subsection{Strictification}

\subsection{Mechanisation}
