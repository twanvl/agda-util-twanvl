{-# OPTIONS --without-K #-}
module Util.Equivalence

open import Util.Equality

open import Data.Product

--------------------------------------------------------------------------------
-- Equivalences
--------------------------------------------------------------------------------

record PreEquivalence {a} (A B : Set a) : Set a where
  field fw : A → B
  field bw : B → A
  field bw-fw : ∀ x → bw (fw x) ≡ x
  field fw-bw : ∀ x → fw (bw x) ≡ x

record Equivalence {a} (A B : Set a) : Set a where
  field fw : A → B
  field bw : B → A
  field bw-fw : ∀ x → bw (fw x) ≡ x
  field fw-bw : ∀ x → fw (bw x) ≡ x
  field adj : ∀ x → cong fw (bw-fw x) ≡ fw-bw (fw x)

mkEquiv : ∀ {a A B} → PreEquivalence {a} A B → Equivalence A B
mkEquiv eq = record
  { fw = fw
  ; bw = bw
  ; bw-fw = adjoint-bw-fw fw-bw bw-fw
  ; fw-bw = fw-bw
  ; adj = adjoint-bw-fw-adjoint }
  where
  open PreEquivalence eq

--------------------------------------------------------------------------------
-- Basic reasoning
--------------------------------------------------------------------------------

idE : ∀ {a A} → Equivalence {a} A A
idE = record { fw = id ; bw = id ; bw-fw = \_ → refl ; fw-bw = \_ → refl ; adj = \_ → refl }

symE : ∀ {a A B} → Equivalence {a} A B → Equivalence B A
symE eq = mkEquiv (record { fw = bw ; bw = fw ; bw-fw = fw-bw ; fw-bw = bw-fw })
  where open Equivalence eq

_∘E_ : ∀ {a A B C} → Equivalence {a} A B → Equivalence B C → Equivalence A C
f ∘E g = mkEquiv record
  { fw = fw g ∘ fw f
  ; bw = bw f ∘ bw g
  ; bw-fw = \x → cong (bw f) (bw-fw g (fw f x)) ⟨ trans ⟩ bw-fw f x 
  ; fw-bw = \x → cong (fw g) (fw-bw f (bw g x)) ⟨ trans ⟩ fw-bw g x
  }
  where
  open Equivalence

module ≈-Reasoning where
  infix  3 _∎'
  infixr 2 _≈⟨_⟩_

  _≈_ : ∀ {a} (A B : Set a) → Set _
  _≈_ = Equivalence
  
  _≈⟨_⟩_ : ∀ {a} (x {y z} : Set a) → x ≈ y → y ≈ z → x ≈ z
  _ ≈⟨ x≡y ⟩ y≡z = x≡y ∘E y≡z

  _∎' : ∀ {a} (x : Set a) → x ≈ x
  _∎' _ = idE

--------------------------------------------------------------------------------
-- Simple equivalences
--------------------------------------------------------------------------------
open ≈-Reasoning

Σ-cong : ∀ {A : Set} {B C : A → Set} → (∀ x → B x ≈ C x) → Σ A B ≈ Σ A C
Σ-cong eq = mkEquiv record
  { fw = \x → proj₁ x , fw (proj₁ x) (proj₂ x)
  ; bw = \x → proj₁ x , bw (proj₁ x) (proj₂ x)
  ; bw-fw = \x → cong-, refl (bw-fw (proj₁ x) (proj₂ x))
  ; fw-bw = \x → cong-, refl (fw-bw (proj₁ x) (proj₂ x))
  }
  where
  module _ (x : _) where
    open Equivalence (eq x) public

Σ-assoc : ∀ {A : Set} {B : A → Set} {C : (x : A) → B x → Set} → (Σ (Σ A B) (uncurry C)) ≈ Σ A (\x → Σ (B x) (C x))
Σ-assoc = mkEquiv record
  { fw = \x → proj₁ (proj₁ x) , proj₂ (proj₁ x) , proj₂ x
  ; bw = _
  ; bw-fw = \_ → refl
  ; fw-bw = \_ → refl
  }
  where
