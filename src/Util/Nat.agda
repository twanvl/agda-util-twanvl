{-# OPTIONS --rewriting --without-K #-}
module Util.Nat where

open import Util.Equality

open import Level using () renaming (zero to lzero)
open import Function
open import Algebra.Structures
open import Relation.Binary hiding (Sym)
open import Relation.Nullary
open import Data.Nat as Nat public
open import Data.Nat.Properties public
open ≤-Reasoning public using (_≤⟨_⟩_) renaming (begin_ to begin≤_;_∎ to _∎≤;_≡⟨_⟩_ to _≡⟨_⟩≤_)
open import Data.Product
open import Data.Sum
open import Data.Empty

--------------------------------------------------------------------------------
-- Induction utilities
--------------------------------------------------------------------------------

open import Induction.Nat using () renaming (<-well-founded to <′-well-founded)
open import Induction.WellFounded

map-acc : ∀ {a b r s A B} {R : Rel {a} A r} {S : Rel {b} B s} (f : B → A)
        → S =[ f ]⇒ R → ∀ {x} → Acc R (f x) → Acc S x
map-acc f sr (acc a) = acc (\_ s → map-acc f sr (a _ (sr s)))

map-acc′ : ∀ {a r A} {R S : Rel {a} A r} → S ⇒ R → ∀ {x} → Acc R x → Acc S x
map-acc′ = map-acc id

map-wf : ∀ {a b r s A B} {R : Rel {a} A r} {S : Rel {b} B s} (f : B → A)
       → S =[ f ]⇒ R → Well-founded R → Well-founded S
map-wf f sr wf-r = map-acc f sr ∘ wf-r ∘ f

map-preserves-acc : ∀ {a b r s p A B} {P : B → Set p} {R : Rel {a} A r} {S : Rel {b} B s} (f : B → A)
                  → (∀ {x y} → P y → S x y → R (f x) (f y))
                  → (∀ {x y} → S y x → P x → P y)
                  → ∀ {x} → P x → Acc R (f x) → Acc S x
map-preserves-acc f sr sp px (acc a) = acc (\_ s → map-preserves-acc f sr sp (sp s px) (a _ (sr px s)))

zip-wf : ∀ {a b c r s t A B C} {R : Rel {b} B r} {S : B → Rel {c} C s} {T : Rel {a} A t}
       → (f : A → B) (g : A → C)
       → (∀ {x y} → T x y → (R (f x) (f y) ⊎ f x ≡ f y × S (f x) (g x) (g y)))
       → Well-founded R → (∀ {x} → Well-founded (S x)) → Well-founded T
zip-wf {R = R} {S = S} {T = T} f g trs wf-r wf-s =
  map-wf (\x → (f x , g x))
         ([ left , (\x → subst (\u → _<ˡ_ (f _ , g _) (u , g _)) (proj₁ x) (right (proj₂ x))) ] ∘ trs)
         (well-founded wf-r wf-s)
  where open Lexicographic R S renaming (_<_ to _<ˡ_)

<-well-founded : Well-founded _<_
<-well-founded = map-acc′ ≤⇒≤′ ∘ <′-well-founded

--------------------------------------------------------------------------------
-- Exposing encapsulated stuff
--------------------------------------------------------------------------------

open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne public using ()
  renaming (+-comm to ⊔-comm; +-assoc to ⊔-assoc; +-identity to ⊔-identity; distrib to ⊔-distrib
           ;*-comm to ⊓-comm; *-assoc to ⊓-assoc)
open IsCommutativeSemiring isCommutativeSemiring public
  using (+-comm; +-assoc; +-identity; *-comm; *-assoc; *-identity)
  renaming (zero to *-zero)
open DecTotalOrder Nat.decTotalOrder public using ()
  renaming (refl to ≤-refl; trans to ≤-trans; reflexive to ≤-reflexive; antisym to ≤-antisym; total to _≤?≥_)
open StrictTotalOrder strictTotalOrder public using ()
  renaming (compare to compare'; irrefl to <-irrefl)

-- rewrites
+-identity₂ : ∀ x → x + 0 ≡ x
+-identity₂ = proj₂ +-identity

*-identity₂ : ∀ x → x * 1 ≡ x
*-identity₂ = proj₂ *-identity

*-zero₂ : ∀ x → x * 0 ≡ 0
*-zero₂ = proj₂ *-zero

{-# REWRITE +-identity₂ #-}
{-# REWRITE *-identity₂ #-}
{-# REWRITE *-zero₂ #-}
{-# REWRITE +-assoc #-}
{-# REWRITE ⊔-assoc #-}
{-# REWRITE ⊓-assoc #-}
{-# REWRITE *-assoc #-}

--------------------------------------------------------------------------------
-- More properties of * and +
--------------------------------------------------------------------------------

*-suc : ∀ x y → x * suc y ≡ x + x * y
*-suc x y = *-comm x (suc y) ⟨ trans ⟩ cong (_+_ x) (*-comm y x)

--------------------------------------------------------------------------------
-- Utility
--------------------------------------------------------------------------------

≥-reflexive : _≡_ ⇒ _≥_
≥-reflexive = ≤-reflexive ∘ sym

_-[_]→_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} → (A → Set ℓ₁) → (A → B) → (B → Set ℓ₂) → Set _
P -[ f ]→ Q = ∀ x → P x → Q (f x)

≤-to-ℕ : ∀ {m n} → m ≤ n → ℕ
≤-to-ℕ z≤n = 0
≤-to-ℕ (s≤s m≤n) = suc (≤-to-ℕ m≤n)

n+0≡n : ∀ n → n + 0 ≡ n
n+0≡n = proj₂ +-identity

--------------------------------------------------------------------------------
-- Properties of ≤
--------------------------------------------------------------------------------

s≤k+s : ∀ k {m n} → m ≤ k + n → suc m ≤ k + suc n
s≤k+s k {m} {n} rewrite +-comm k (suc n) | +-comm n k = s≤s

≤-unstep : ∀ {m n} → suc m ≤ n → m ≤ n
≤-unstep = ≤-pred ∘ ≤-step

{-
data Ordering' (m n : ℕ) : Set where
  less    : m < n → Ordering' m n
  equal   : m ≡ n → Ordering' m n
  greater : m > n → Ordering' m n

compare' : ∀ m n → Ordering' m n
compare' zero zero = equal refl
compare' zero (suc n) = less (s≤s z≤n)
compare' (suc m) zero = greater (s≤s z≤n)
compare' (suc m) (suc n) with compare' m n
... | less    mn = less (s≤s mn)
... | equal   mn = equal (cong suc mn)
... | greater mn = greater (s≤s mn)
-}

_≤?>_ : ∀ m n → m ≤ n ⊎ m > n
m ≤?> n with m ≤? n
... | yes m≤n = inj₁ m≤n
... | no ¬m≤n = inj₂ (≰⇒> ¬m≤n)

_<?≥_ : ∀ m n → m < n ⊎ m ≥ n
m <?≥ n with n ≤? m
... | yes n≤m = inj₂ n≤m
... | no ¬n≤m = inj₁ (≰⇒> ¬n≤m)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ {zero} {suc j} (s≤s x) = \()
<⇒≢ {suc i} {suc j} (s≤s x) = <⇒≢ x ∘ cong pred

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (s≤s z≤n) = \()
<⇒≱ (s≤s (s≤s x)) = <⇒≱ (s≤s x) ∘ ≤-pred

from-z≤n : ∀ {m} → m ≤ 0 → m ≡ 0
from-z≤n z≤n = refl

data Ordering-l : ℕ → ℕ → Set where
  less          : ∀ m k → Ordering-l m (suc (m + k))
  greater-equal : ∀ m k → Ordering-l (m + k) m

compare-l : ∀ m n → Ordering-l m n
compare-l m       zero    = greater-equal zero m
compare-l zero    (suc n) = less zero n
compare-l (suc m) (suc n) with compare-l m n
compare-l (suc ._) (suc ._) | less          a b = less          (suc a) b
compare-l (suc ._) (suc ._) | greater-equal a b = greater-equal (suc a) b

≤-to-< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤-to-< m≤n m≢n with ≤⇒≤′ m≤n
≤-to-< m≤n m≢n | ≤′-refl = ⊥-elim (m≢n refl)
≤-to-< m≤n m≢n | ≤′-step x = s≤s (≤′⇒≤ x)

pred-n≤n : ∀ n → pred n ≤ n
pred-n≤n n = pred-mono (≤-step (≤-refl {n}))

suc-pred : ∀ {a b} → a > b → suc (pred a) ≡ a
suc-pred (s≤s x) = refl

≤-unique : ∀ {m n} → (x y : m ≤ n) → x ≡ y
≤-unique z≤n z≤n = refl
≤-unique (s≤s x) (s≤s y) = cong s≤s (≤-unique x y)

--------------------------------------------------------------------------------
-- Properties of ≤′ and other relations
--------------------------------------------------------------------------------

≤′-trans : Transitive _≤′_
≤′-trans x ≤′-refl = x
≤′-trans x (≤′-step y) = ≤′-step (≤′-trans x y)

compare′ : Trichotomous _≡_ _<′_
compare′ m n with compare' m n
... | tri< a b c = tri< (≤⇒≤′ a) b (c ∘ ≤′⇒≤)
... | tri≈ a b c = tri≈ (a ∘ ≤′⇒≤) b (c ∘ ≤′⇒≤)
... | tri> a b c = tri> (a ∘ ≤′⇒≤) b (≤⇒≤′ c)

<′⇒≢ : _<′_ ⇒ _≢_
<′⇒≢ = <⇒≢ ∘ ≤′⇒≤

_≤′?_ : ∀ m n → Dec (m ≤′ n)
m ≤′? n with m ≤? n
... | yes m≤n = yes (≤⇒≤′ m≤n)
... | no ¬m≤n = no (¬m≤n ∘ ≤′⇒≤)

--------------------------------------------------------------------------------
-- Properties of ⊔
--------------------------------------------------------------------------------

n≤m⊔n : ∀ m n → n ≤ m ⊔ n
n≤m⊔n m n rewrite ⊔-comm m n = m≤m⊔n n m

⊔≤ : ∀ {m n o} → m ≤ o → n ≤ o → m ⊔ n ≤ o
⊔≤ z≤n n≤o = n≤o
⊔≤ (s≤s m≤o) z≤n = s≤s m≤o
⊔≤ (s≤s m≤o) (s≤s n≤o) = s≤s (⊔≤ m≤o n≤o)

_⊔-mono_ : ∀ {a b c d} → a ≤ b → c ≤ d → a ⊔ c ≤ b ⊔ d
_⊔-mono_ {a} {b} {c} {d} a≤b c≤d = ⊔≤ (≤-trans a≤b (m≤m⊔n b d)) (≤-trans c≤d (n≤m⊔n b d))

n⊔n≡n : ∀ n → n ⊔ n ≡ n
n⊔n≡n zero = refl
n⊔n≡n (suc n) = cong suc (n⊔n≡n n)

n⊔n≤n : ∀ {n} → n ⊔ n ≤ n
n⊔n≤n {n} = ≤-reflexive (n⊔n≡n n)

+⊔-distr₁ : ∀ a b c → a + (b ⊔ c) ≡ (a + b) ⊔ (a + c)
+⊔-distr₁ zero b c = refl
+⊔-distr₁ (suc a) b c = cong suc (+⊔-distr₁ a b c)
{-# REWRITE +⊔-distr₁ #-}

+⊔-distr₂ : ∀ a b c → (a ⊔ b) + c ≡ (a + c) ⊔ (b + c)
+⊔-distr₂ a b c = +-comm (a ⊔ b) c ⟨ trans ⟩ +⊔-distr₁ c a b ⟨ trans ⟩ cong₂ _⊔_ (+-comm c a) (+-comm c b)
{-# REWRITE +⊔-distr₂ #-}

⊔⊔-distr₂ : ∀ a b c → (a ⊔ c) ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ c
⊔⊔-distr₂ a b c =
  ⊔-assoc a c (b ⊔ c) ⟨ trans ⟩
  cong (_⊔_ a) (⊔-comm c (b ⊔ c) ⟨ trans ⟩ ⊔-assoc b c c ⟨ trans ⟩ cong (_⊔_ b) (n⊔n≡n c)) ⟨ trans ⟩
  sym (⊔-assoc a b c)

+⊔-comm : ∀ a b c d → (a + b) ⊔ (c + d) ≤ (a ⊔ c) + (b ⊔ d)
+⊔-comm a b c d =
  begin≤
    (a + b) ⊔ (c + d)
  ≤⟨ ((m≤m⊔n a c) +-mono ≤-refl {b}) ⊔-mono ((n≤m⊔n a c) +-mono ≤-refl {d}) ⟩
    ((a ⊔ c) + b) ⊔ ((a ⊔ c) + d)
  ≡⟨ sym (+⊔-distr₁ (a ⊔ c) b d) ⟩≤
    (a ⊔ c) + (b ⊔ d)
  ∎≤

⊔-pred : ∀ a b → pred a ⊔ pred b ≡ pred (a ⊔ b)
⊔-pred zero b = refl
⊔-pred (suc a) zero = proj₂ ⊔-identity a
⊔-pred (suc a) (suc b) = refl

⊔-large₁ : ∀ {a b} → a ≥ b → a ⊔ b ≡ a
⊔-large₁ {a} {b} ab = ≤-antisym (⊔≤ ≤-refl ab) (m≤m⊔n a b)

⊔-large₂ : ∀ {a b} → a ≤ b → a ⊔ b ≡ b
⊔-large₂ {a} {b} ab = ≤-antisym (⊔≤ ab ≤-refl) (n≤m⊔n a b)

⊔-idemp : ∀ a → a ⊔ a ≡ a
⊔-idemp a = ⊔-large₁ ≤-refl
{-# REWRITE ⊔-idemp #-}

⊔-comm₂ : ∀ a b c → a ⊔ (b ⊔ c) ≡ b ⊔ (a ⊔ c)
⊔-comm₂ a b c = cong (flip _⊔_ c) (⊔-comm a b)

⊔-comm₂' : ∀ a b c → a ⊔ b ⊔ c ≡ a ⊔ c ⊔ b
⊔-comm₂' a b c = ⊔-assoc a b c ⟨ trans ⟩
                cong (_⊔_ a) (⊔-comm b c) ⟨ trans ⟩
                sym (⊔-assoc a c b)

⊔-distr₁ : ∀ a b c → a ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ (a ⊔ c)
⊔-distr₁ zero b c = refl
⊔-distr₁ (suc a) zero c = cong (flip _⊔_ c) (sym (⊔-idemp (suc a))) ⟨ trans ⟩ ⊔-assoc (suc a) (suc a) c
⊔-distr₁ (suc a) (suc b) zero = cong suc (cong (flip _⊔_ b) (sym (⊔-idemp a)) ⟨ trans ⟩ ⊔-comm₂' a a b)
⊔-distr₁ (suc a) (suc b) (suc c) = cong suc (⊔-distr₁ a b c)
--{-# REWRITE ⊔-distr₁ #-}

⊔-suc-pred : ∀ a b → suc (pred a) ⊔ suc b ≡ a ⊔ suc b
⊔-suc-pred zero b = refl
⊔-suc-pred (suc a) b = refl

--------------------------------------------------------------------------------
-- Properties of ⊓
--------------------------------------------------------------------------------

m⊓n≤n : ∀ m n → m ⊓ n ≤ n
m⊓n≤n m n rewrite ⊓-comm m n = m⊓n≤m n m

≤⊓ : ∀ {m n o} → m ≤ n → m ≤ o → m ≤ n ⊓ o
≤⊓ z≤n m≤o = z≤n
≤⊓ (s≤s m≤n) (s≤s m≤o) = s≤s (≤⊓ m≤n m≤o)

m⊓n≡n : ∀ {m n} → n ≤ m → m ⊓ n ≡ n
m⊓n≡n {m} {n} mn = ≤-antisym (m⊓n≤n m n) (≤⊓ mn ≤-refl)

⊓-small₁ : ∀ {a b} → a ≤ b → a ⊓ b ≡ a
⊓-small₁ {a} {b} ab = ≤-antisym (m⊓n≤m a b) (≤⊓ ≤-refl ab)

⊓-small₂ : ∀ {a b} → a ≥ b → a ⊓ b ≡ b
⊓-small₂ {a} {b} ab = ≤-antisym (m⊓n≤n a b) (≤⊓ ab ≤-refl)

--------------------------------------------------------------------------------
-- Properties of ∸
--------------------------------------------------------------------------------

{-
_∸-mono_ : ∀ {a b c d} → a ≤ c → b ≥ d → (a ∸ b) ≤ (c ∸ d)
_∸-mono_ {a} {b} ac z≤n = ≤-trans (n∸m≤n b a) ac
z≤n    ∸-mono s≤s bd = z≤n
s≤s ac ∸-mono s≤s bd = {!!} --ac ∸-mono bd
-}

{-
n∸n≡0 : ∀ n → n ∸ n ≡ 0
n∸n≡0 zero    = refl
n∸n≡0 (suc n) = n∸n≡0 n
-}

--⊔+-mono : ∀ a b c d e f → 
--a ≤ b + (a ∸ b)  n≤m+n∸m

--≤-cong₂-+ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
--≤-cong₂-+ {a} {b} {c} {d} = _+-mono_

m+n∸m≡n' : ∀ m n → m + n ∸ m ≡ n
m+n∸m≡n' zero zero = refl
m+n∸m≡n' zero (suc n) = refl
m+n∸m≡n' (suc m) n = m+n∸m≡n' m n

m+n∸n≤m : ∀ m n → m + n ∸ n ≤ m
m+n∸n≤m m n = ≤-reflexive (m+n∸n≡m m n)

m+n∸m≥n : ∀ m n → m + (n ∸ m) ≥ n
m+n∸m≥n zero n = ≤-refl
m+n∸m≥n (suc m) zero = z≤n
m+n∸m≥n (suc m) (suc n) = s≤s (m+n∸m≥n m n)

m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
m≤n⇒m∸n≡0 {n = n} z≤n = 0∸n≡0 n
m≤n⇒m∸n≡0 (s≤s m≤n) = m≤n⇒m∸n≡0 m≤n

m∸n+n∸o≡m∸o : ∀ {m n o} → m ≤ n → n ≤ o → (m ∸ n) + (n ∸ o) ≡ m ∸ o
m∸n+n∸o≡m∸o z≤n z≤n = refl
m∸n+n∸o≡m∸o z≤n (s≤s n≤o) = m≤n⇒m∸n≡0 n≤o
m∸n+n∸o≡m∸o (s≤s m≤n) (s≤s n≤o) = m∸n+n∸o≡m∸o m≤n n≤o

m∸o≤m∸n+n∸o : ∀ {m n o} → m ≤ n → n ≤ o → m ∸ o ≤ (m ∸ n) + (n ∸ o)
m∸o≤m∸n+n∸o m≤n n≤o = ≥-reflexive (m∸n+n∸o≡m∸o m≤n n≤o)

n∸m+o∸n≡o∸m : ∀ {m n o} → m ≤ n → n ≤ o → (n ∸ m) + (o ∸ n) ≡ o ∸ m
n∸m+o∸n≡o∸m z≤n z≤n = refl
n∸m+o∸n≡o∸m z≤n (s≤s n≤o) = cong suc (n∸m+o∸n≡o∸m z≤n n≤o)
n∸m+o∸n≡o∸m (s≤s m≤n) (s≤s n≤o) = n∸m+o∸n≡o∸m m≤n n≤o

o∸m≤n∸m+o∸n : ∀ {m n o} → m ≤ n → n ≤ o → o ∸ m ≤ (n ∸ m) + (o ∸ n)
o∸m≤n∸m+o∸n m≤n n≤o = ≥-reflexive (n∸m+o∸n≡o∸m m≤n n≤o)

∸⇒≤ : ∀ m n {k} → m ∸ n ≡ suc k → suc n ≤ m
∸⇒≤ zero zero ()
∸⇒≤ zero (suc n) ()
∸⇒≤ (suc m) zero mn = s≤s z≤n
∸⇒≤ (suc m) (suc n) mn = s≤s (∸⇒≤ _ _ mn)

∸-pred : ∀ m n → m ∸ suc n ≡ pred (m ∸ n)
∸-pred zero zero = refl
∸-pred (suc m) zero = refl
∸-pred zero (suc n) = refl
∸-pred (suc m) (suc n) = ∸-pred m n

--------------------------------------------------------------------------------
-- Properties of ≤
--------------------------------------------------------------------------------

{-
≤-confluent : Confluent _≤_
≤-confluent {a} {b} {c} ab ac = m≤m⊔n b c || n≤m⊔n b c
-}

≤+₁ : ∀ m {n o} → m + n ≤ o → m ≤ o
≤+₁ m {n} = ≤-trans (m≤m+n m n)

≤+₂ : ∀ m {n o} → m + n ≤ o → n ≤ o
≤+₂ m {n} = ≤-trans (n≤m+n m n)

<+₂ : ∀ m {n o} → m + n < o → n < o
<+₂ m {n} = ≤-trans (s≤s (n≤m+n m n))

≤+₁' : ∀ {m n} o → m ≤ n → m ≤ o + n
≤+₁' o mn = z≤n {o} +-mono mn

≤+₂' : ∀ {m n} o → m ≤ n → m ≤ n + o
≤+₂' {n = n} o mn = ≤-trans mn (m≤m+n n o)

≤⊔₁ : ∀ m {n o} → m ⊔ n ≤ o → m ≤ o
≤⊔₁ m {n} = ≤-trans (m≤m⊔n m n)

≤⊔₂ : ∀ m {n o} → m ⊔ n ≤ o → n ≤ o
≤⊔₂ m {n} = ≤-trans (n≤m⊔n m n)

+-comm₂ : ∀ a b c → a + (b + c) ≡ b + (a + c)
+-comm₂ a b c = cong (flip _+_ c) (+-comm a b)

+-comm₃ : ∀ a b c → a + (b + c) ≡ c + (a + b)
+-comm₃ a b c =
  cong (_+_ a) (+-comm b c) ⟨ trans ⟩ +-comm₂ a c b

m∸n+n≡m⊔n : ∀ m n → m ∸ n + n ≡ m ⊔ n
m∸n+n≡m⊔n zero n = cong (flip _+_ n) (0∸n≡0 n)
m∸n+n≡m⊔n (suc m) zero = cong suc (proj₂ +-identity m)
m∸n+n≡m⊔n (suc m) (suc n) = +-comm₂ (m ∸ n) 1 n ⟨ trans ⟩ cong suc (m∸n+n≡m⊔n m n)

a∸b⊔c+b∸c≡a⊔b∸c : ∀ a b c → a ∸ (b ⊔ c) + (b ∸ c) ≡ a ⊔ b ∸ c
a∸b⊔c+b∸c≡a⊔b∸c zero b c = cong (flip _+_ (b ∸ c)) (0∸n≡0 (b ⊔ c))
a∸b⊔c+b∸c≡a⊔b∸c (suc a) zero c = cong (_+_ (suc a ∸ c)) (0∸n≡0 c) ⟨ trans ⟩ proj₂ +-identity (suc a ∸ c)
a∸b⊔c+b∸c≡a⊔b∸c (suc a) (suc b) zero = +-comm₂ (a ∸ b) 1 b ⟨ trans ⟩ cong suc (m∸n+n≡m⊔n a b)
a∸b⊔c+b∸c≡a⊔b∸c (suc a) (suc b) (suc c) = a∸b⊔c+b∸c≡a⊔b∸c a b c

+-pred : ∀ a b {c} → b > c → a + pred b ≡ pred (a + b)
+-pred a zero ()
+-pred a (suc b) bc = sym (cong pred (+-comm₂ a 1 b))


{-
+-∸-assoc : ∀ m n o → n ≥ o → m + (n ∸ o) ≡ m + n ∸ o
+-∸-assoc m n zero z≤n = refl
+-∸-assoc m (suc n) (suc o) (s≤s n≥o) =
  (+-∸-assoc m n o n≥o) ⟨ trans ⟩ cong (flip _∸_ (suc o)) (+-comm₂ 1 m n)
-}

_<+-mono₁_ : ∀ {m n} → m < n → (o : ℕ) → m + o < n + o
_<+-mono₁_ mn o = mn +-mono ≤-refl {o}

_<+-mono₂_ : ∀ m {n o} → n < o → m + n < m + o
_<+-mono₂_ m {n} nno = ≤-reflexive (+-comm₂ 1 m n) ⟨ ≤-trans ⟩ ≤-refl {m} +-mono nno

+0₁ : ∀ {m n} → m + n ≡ 0 → m ≡ 0
+0₁ {zero} _ = refl
+0₁ {suc _} ()

+0₂ : ∀ {m n} → m + n ≡ 0 → n ≡ 0
+0₂ {zero} r = r
+0₂ {suc _} ()

≤+-assoc : ∀ m n o → m + n + o ≤ m + (n + o)
≤+-assoc m n o = ≤-reflexive (+-assoc m n o)

≤+-assoc' : ∀ m n o → m + (n + o) ≤ m + n + o
≤+-assoc' m n o = ≥-reflexive (+-assoc m n o)

_+-unmono_ : ∀ a {m n} → (a + m) ≤ (a + n) → m ≤ n
zero  +-unmono m≤n = m≤n
suc a +-unmono s≤s m≤n = a +-unmono m≤n

--------------------------------------------------------------------------------
-- Pointwise inequality
--------------------------------------------------------------------------------

_≤·_ : ∀ {A} → Rel (A → ℕ) lzero
f ≤· g = ∀ x → f x ≤ g x

_≥·_ : ∀ {A} → Rel (A → ℕ) lzero
_≥·_ = flip _≤·_

_+·_ : ∀ {A : Set} → (A → ℕ) → (A → ℕ) → (A → ℕ)
f +· g = \x → f x + g x

_⊔·_ : ∀ {A : Set} → (A → ℕ) → (A → ℕ) → (A → ℕ)
f ⊔· g = \x → f x ⊔ g x
