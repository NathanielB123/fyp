%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils

module Report.Interim.c8_extension_types where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Extension Types}
\labch{ext}

Typing rule for smart if using extension types

\begin{spec}
if : ∀ (A : Type) (b : Bool) 
       (Att : {Type | b >rw true  ▷ A})
       (Aff : {Type | b >rw false ▷ A})
   → outS(Att) → outS(Aff) → A                     
\end{spec}

Let's revisit our classic example using this typing rule:

%TODO: This doesn't actually work!!
%|f TT ≢ FF| in the false branch of the outer |if|!
\begin{spec}
f3 : ∀ (f : 𝔹 → 𝔹) b → f b ≡ f (f (f b))
f3 f TT 
  = if (A = f TT ≡ f (f (f TT))) (b = f TT)
       (Att = inS(TT ≡ TT)) (Aff = inS(FF ≡ f (f FF)))
       refl
       (if (A = FF ≡ f (f FF) (b = f FF)) (b = f FF)
           (Att = inS(FF ≡ FF)) (Aff = inS(FF ≡ FF))
           refl refl)
\end{spec}:≡

Not too bad! Of course, we would expect |Att| and |Aff| to be inferrable,
but I'm sure inference for extension types has at least some meta-theory.

I guess the nice thing with this technique is that every subterm is still
basically in the same context. i.e. it delegates binding propositions
(in our case, equations) to the extension types. 

Note also that the equational assumptuon is only used in a conversion 
pre-condition (i.e. that |Att == A|). Typing of the LHS and RHS must be
possible independently of the equation. This is a bit more restrictive
than ordinary smart case, but perhaps in a good way.


\begin{spec}
bad : ∀ (f : 𝔹 → 𝔹)
\end{spec}
