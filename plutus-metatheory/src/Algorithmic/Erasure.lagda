\begin{code}
{-# OPTIONS --rewriting #-}

module Algorithmic.Erasure where
\end{code}

\begin{code}
open import Algorithmic as A
open import Untyped
open import Untyped.RenamingSubstitution as U
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Utils
open import Type
open import Type.BetaNBE.RenamingSubstitution
open import Function hiding (_∋_)
open import Builtin hiding (length)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as DC renaming (TermCon to TyTermCon)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AC renaming (TermCon to TyTermCon)
open import Type.RenamingSubstitution as T
open import Type.Equality
open import Type.BetaNBE.Soundness
open import Utils


open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc)
open import Data.List using (List;length;[];_∷_)
open import Data.Vec hiding (length)
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
len : ∀{Φ} → Ctx Φ → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)
\end{code}

\begin{code}
eraseVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *} → AC.TyTermCon A → TermCon
eraseTC (AC.integer i)    = integer i
eraseTC (AC.bytestring b) = bytestring b
eraseTC (AC.string s)     = string s
eraseTC (AC.bool b)       = bool b
eraseTC AC.unit           = unit
eraseTC (AC.Data d)       = Data d

erase : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → len Γ ⊢
erase (` α)                = ` (eraseVar α)
erase (ƛ t)                = ƛ (erase t) 
erase (t · u)              = erase t · erase u
erase (Λ t)                = delay (erase t)
erase (_·⋆_ t A)           = force (erase t)
erase (wrap A B t)         = erase t
erase (unwrap t)           = erase t
erase {Γ = Γ} (con t)      = con (eraseTC {Γ = Γ} t)
erase (builtin b)          = builtin b
erase (error A)            = error
\end{code}

Porting this from declarative required basically deleting one line but
I don't think I can fully exploit this by parameterizing the module as
I need to pattern match on the term constructors

# Erasing decl/alg terms agree

\begin{code}
open import Relation.Binary.PropositionalEquality
import Declarative as D
import Declarative.Erasure as D
open import Algorithmic.Completeness

open import Utils

lenLemma : ∀ {Φ}(Γ : D.Ctx Φ) → len (nfCtx Γ) ≡ D.len Γ
lenLemma D.∅        = refl
lenLemma (Γ D.,⋆ J) = lenLemma Γ
lenLemma (Γ D., A)  = cong suc (lenLemma Γ)

lenLemma⋆ : ∀ Φ → D.len⋆ Φ ≡ len⋆ Φ
lenLemma⋆ ∅       = refl
lenLemma⋆ (Φ ,⋆ K) = cong suc (lenLemma⋆ Φ)

-- these lemmas for each clause of eraseVar and erase below could be
-- avoided by using with but it would involve doing with on a long
-- string of arguments, both contexts, equality proof above, and
-- before and after versions of all arguments and all recursive calls

lemzero : ∀{n n'}(p : suc n ≡ suc n') → zero ≡ subst Fin p zero
lemzero refl = refl

lemsuc : ∀{n n'}(p : suc n ≡ suc n')(q : n ≡ n')(i : Fin n) →
  suc (subst Fin q i) ≡ subst Fin p (suc i)
lemsuc refl refl i = refl

open import Type.BetaNormal.Equality
open import Function

sameTC : ∀{Φ Γ}{A : Φ ⊢⋆ *}(tcn : DC.TyTermCon A)
  → D.eraseTC {Γ = Γ} tcn ≡ eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)
sameTC (DC.integer i)    = refl
sameTC (DC.bytestring b) = refl
sameTC (DC.string s)     = refl
sameTC (DC.bool b)       = refl
sameTC DC.unit           = refl
sameTC (DC.Data d)       = refl

lem≡Ctx : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡ Γ' → len Γ ≡ len Γ'
lem≡Ctx refl = refl

lem-conv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ A.∋ A)
  → subst Fin (lem≡Ctx p) (eraseVar x)  ≡ eraseVar (conv∋ p q x)
lem-conv∋ refl refl x = refl

sameVar : ∀{Φ Γ}{A : Φ ⊢⋆ *}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst Fin (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} D.Z     = lemzero (cong suc (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x) = trans
  (sameVar x)
  (cong (subst Fin (lenLemma Γ)) (lem-conv∋ refl (ren-nf S A) (T (nfTyVar x))))

lemVar : ∀{n n'}(p : n ≡ n')(i : Fin n) →  ` (subst Fin p i) ≡ subst _⊢ p (` i)
lemVar refl i = refl

lemƛ : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : suc n ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)  
lemƛ refl refl t = refl

lem· : ∀{n n'}(p : n ≡ n')(t u : n ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lem-delay : ∀{n n'}(p : n ≡ n')(t : n ⊢) → delay (subst _⊢ p t) ≡ subst _⊢ p (delay t)
lem-delay refl t = refl

lem-force : ∀{n n'}(p : n ≡ n')(t : n ⊢) → force (subst _⊢ p t) ≡ subst _⊢ p (force t)
lem-force refl t = refl

lem-weaken : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : n ⊢)
  → U.weaken (subst _⊢ p t) ≡ subst _⊢ q (U.weaken t)
lem-weaken refl refl t = refl

lemcon' : ∀{n n'}(p : n ≡ n')(tcn : TermCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{n n'}(p : n ≡ n') →  error ≡ subst _⊢ p error
lemerror refl = refl

lembuiltin : ∀{n n'}(b : Builtin)(p : n ≡ n') →  builtin b ≡ subst _⊢ p (builtin b)
lembuiltin b refl = refl


lem[]' : ∀{n n'}(p : n ≡ n') →
  [] ≡ subst (λ n → Vec (n ⊢) 0) p []
lem[]' refl = refl

lem[]'' : ∀{n n'}(p : n ≡ n') →
  [] ≡ subst (λ n → Vec (n ⊢) 0) p []
lem[]'' refl = refl

lem∷ : ∀{m n n'}(p : n ≡ n')(t : n ⊢)(ts : Vec (n ⊢) m)
  → subst _⊢ p t ∷ subst (λ n → Vec (n ⊢) m) p ts ≡ subst (λ n → Vec (n ⊢) (suc m)) p (t ∷ ts) 
lem∷ refl t ts = refl

lem∷' : ∀{A : Set}{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : A)(ts : Vec A n)
  → t ∷ subst (Vec A) p ts ≡ subst (Vec A) q (t ∷ ts) 
lem∷' refl refl t ts = refl

{-
lemTel : ∀{m n n'}(p : n ≡ n')(bn : Builtin)(ts : Vec (n ⊢) m)
  → (q : m ≤‴ arity bn)
  → builtin bn q (subst (λ n → Vec (n ⊢) m) p ts)
    ≡ subst _⊢ p (builtin bn q ts)
lemTel refl bn ts q = refl
-}

lem-erase : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(t : Γ A.⊢ A)
  → subst _⊢ (lem≡Ctx p) (erase t)  ≡ erase (conv⊢ p q t)
lem-erase refl refl t = refl

lem-subst : ∀{n}(t : n ⊢)(p : n ≡ n) → subst _⊢ p t ≡ t
lem-subst t refl = refl

{-
lem-builtin : ∀{m n n'}(b : Builtin)(ts : Untyped.Tel n m)
  → (p : n ≤‴ arity b)
  → (q : n' ≤‴ arity b)
  → (r : n ≡ n')
  → Untyped.builtin b p ts ≡ builtin b q (subst (Vec (m ⊢)) r ts)
lem-builtin b ts p q refl = cong (λ p → builtin b p ts) (lem≤‴ p q)
-}

lem-erase' : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(q : A ≡ A')(t : Γ A.⊢ A)
  → erase t  ≡ erase (conv⊢ refl q t)
lem-erase' {Γ = Γ} p t = trans
  (sym (lem-subst (erase t) (lem≡Ctx {Γ = Γ} refl)))
  (lem-erase refl p t)

same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 
subst++ : ∀{A : Set}{m m' n n'}
  → (as : Vec A m)
  → (as' : Vec A n)
  → (p : m ≡ m')
  → (q : n ≡ n')
  → (r : m + n ≡ m' + n')
  → subst (Vec A) r (as ++ as')
    ≡ subst (Vec A) p as ++ subst (Vec A) q as'
subst++ as as' refl refl refl = refl

subst++' : ∀{o o' m n}
  → (as : Vec (o ⊢) m)
  → (as' : Vec (o ⊢) n)
  → (p : o ≡ o')
  → subst (λ o → Vec (o ⊢) (m + n)) p (as ++ as')
    ≡ subst (λ o → Vec (o ⊢) m) p as ++ subst (λ o → Vec (o ⊢) n) p as'
subst++' as as' refl = refl

+cancel : ∀{m m' n n'} → m + n ≡ m' + n' → m ≡ m' → n ≡ n'
+cancel p refl = +-cancelˡ-≡ _ p

open import Data.Unit
same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ t) = trans
  (cong ƛ (same t))
  (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t)))
same {Γ = Γ} (t D.· u) = trans
  (cong₂ _·_ (same t) (same u))
  (lem· (lenLemma Γ) (erase (nfType t)) (erase (nfType u)))
same {Γ = Γ} (D.Λ {B = B} t) = trans
  (trans (cong delay (same t))
         (lem-delay (lenLemma Γ) (erase (nfType t))))
  (cong (subst _⊢ (lenLemma Γ) ∘ delay)
        (lem-erase' (subNf-lemma' B) (nfType t)))
same {Γ = Γ} (D._·⋆_ {B = B} t A) = trans
  (trans (cong force (same t))
         (lem-force (lenLemma Γ) (erase (nfType t))))
  (cong (subst _⊢ (lenLemma Γ))
        (trans (cong force (lem-erase' (lemΠ B) (nfType t)))
        (lem-erase' (lem[] A B) (conv⊢ refl (lemΠ B) (nfType t) ·⋆ nf A))))
same {Γ = Γ} (D.wrap A B t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (stability-μ A B) (nfType t)))
same {Γ = Γ} (D.unwrap {A = A}{B = B} t) = trans
  (same t)
  (cong
    (subst _⊢ (lenLemma Γ))
    (lem-erase' (sym (stability-μ A B)) (unwrap (nfType t)))) 
same {Γ = Γ} (D.conv p t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (completeness p) (nfType t)))
same {Γ = Γ} (D.con tcn) = trans
  (cong con (sameTC {Γ = Γ} tcn))
  (lemcon' (lenLemma Γ) (eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)))

same {Γ = Γ} (D.builtin b) = trans
  (lembuiltin b (lenLemma Γ)) (cong (subst _⊢ (lenLemma Γ))
  (lem-erase refl (btype-lem b) (builtin b)))
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)

open import Algorithmic.Soundness

same'Len : ∀ {Φ}(Γ : A.Ctx Φ) → D.len (embCtx Γ) ≡ len Γ
same'Len ∅          = refl
same'Len (Γ ,⋆ J)   = same'Len Γ
same'Len (Γ , A)    = cong suc (same'Len Γ)

lem-Dconv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ D.∋ A)
  → subst Fin (cong D.len p) (D.eraseVar x)  ≡ D.eraseVar (D.conv∋ p q x)
lem-Dconv∋ refl refl x = refl

same'Var : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.∋ A)
  →  eraseVar x ≡ subst Fin (same'Len Γ) (D.eraseVar (embVar x))
same'Var {Γ = Γ , _} Z     = lemzero (cong suc (same'Len Γ))
same'Var {Γ = Γ , _} (S x) = trans
  (cong suc (same'Var x))
  (lemsuc (cong suc (same'Len Γ)) (same'Len Γ) (D.eraseVar (embVar x)))
same'Var {Γ = Γ ,⋆ _} (T {A = A} x) = trans
  (same'Var x)
  (cong (subst Fin (same'Len Γ)) (lem-Dconv∋ refl (sym (ren-embNf S A))
        (D.T (embVar x))))

same'TC : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(tcn : AC.TyTermCon A)
  → eraseTC {Γ = Γ} tcn ≡ D.eraseTC {Φ}{Γ = embCtx Γ} (embTC tcn)
same'TC (AC.integer i)    = refl
same'TC (AC.bytestring b) = refl
same'TC (AC.string s)     = refl
same'TC (AC.bool b)       = refl
same'TC AC.unit           = refl
same'TC (AC.Data d)       = refl

same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.⊢ A)
  →  erase x ≡ subst _⊢ (same'Len Γ) (D.erase (emb x))
same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (D.eraseVar (embVar x)))
same' {Γ = Γ} (ƛ t) = trans
  (cong ƛ (same' t))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (D.erase (emb t)))
same' {Γ = Γ} (t · u) = trans
  (cong₂ _·_ (same' t) (same' u))
  (lem· (same'Len Γ) (D.erase (emb t)) (D.erase (emb u)))
same' {Γ = Γ} (Λ t) =  trans
  (cong delay (same' t))
  (lem-delay (same'Len Γ) (D.erase (emb t)))
same' {Γ = Γ} (t ·⋆ A)   = trans
  (cong force (same' t))
  (lem-force (same'Len Γ) (D.erase (emb t)))
same' {Γ = Γ} (wrap A B t)   = same' t
same' {Γ = Γ} (unwrap t) = same' t
same' {Γ = Γ} (con x) = trans
  (cong con (same'TC {Γ = Γ} x))
  (lemcon' (same'Len Γ) (D.eraseTC {Γ = embCtx Γ}(embTC x)))
same' {Γ = Γ} (builtin b) = lembuiltin b (same'Len Γ)
same' {Γ = Γ} (error A) = lemerror (same'Len Γ)
\end{code}
