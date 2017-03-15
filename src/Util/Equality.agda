{-# OPTIONS --rewriting --without-K #-}
module Util.Equality where

open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Function
open ≡-Reasoning public

-- We use rewriting
{-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------------------
-- trans and sym:
-- rewrite equations with trans and sym to normal form
--------------------------------------------------------------------------------

trans-sym : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
trans-sym xy zy = trans xy (sym zy)


trans-refl : ∀ {a} {A : Set a} {x y : A} → (x≡y : x ≡ y) → trans x≡y refl ≡ x≡y
trans-refl refl = refl
{-# REWRITE trans-refl #-}


trans-assoc : ∀ {a} {A : Set a} {x y z w : A} (x≡y : x ≡ y) (y≡z : y ≡ z) (z≡w : z ≡ w)
            → trans (trans x≡y y≡z) z≡w ≡ trans x≡y (trans y≡z z≡w)
trans-assoc relf refl refl = refl
{-# REWRITE trans-assoc #-}


trans-sym₁ : ∀ {a} {A : Set a} {x y : A} → (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl
trans-sym₁ refl = refl
{-# REWRITE trans-sym₁ #-}

trans-sym₂ : ∀ {a} {A : Set a} {x y : A} → (x≡y : x ≡ y) → trans x≡y (sym x≡y) ≡ refl
trans-sym₂ refl = refl
{-# REWRITE trans-sym₂ #-}

trans-trans-sym₁ : ∀ {a} {A : Set a} {x y z : A} → (x≡y : x ≡ y) → (y≡z : y ≡ z) → trans (sym x≡y) (trans x≡y y≡z) ≡ y≡z
trans-trans-sym₁ refl _ = refl
{-# REWRITE trans-trans-sym₁ #-}

trans-trans-sym₂ : ∀ {a} {A : Set a} {x y z : A} → (x≡y : x ≡ y) → (x≡z : x ≡ z) → trans x≡y (trans (sym x≡y) x≡z) ≡ x≡z
trans-trans-sym₂ refl _ = refl
{-# REWRITE trans-trans-sym₂ #-}

--------------------------------------------------------------------------------
-- Rewriting with cong and subst
--------------------------------------------------------------------------------

cong-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : B → C) {x y : A} (g : A → B)
          → (x≡y : x ≡ y) → cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y
cong-cong f g refl = refl
{-# REWRITE cong-cong #-}

subst-subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y z} → (x≡y : x ≡ y) → (y≡z : y ≡ z) → (px : P x)
            → subst P y≡z (subst P x≡y px) ≡ subst P (trans x≡y y≡z) px
subst-subst P refl refl px = refl
{-# REWRITE subst-subst #-}

subst-cong : ∀ {a b c} {A : Set a} {B : Set b} (C : B → Set c) (f : A → B) {x y : A} (x≡y : x ≡ y)
           → subst C (cong f x≡y) ≡ subst (C ∘ f) x≡y
subst-cong C f refl = refl
{-# REWRITE subst-cong #-}

subst-const : ∀ {a b} {A : Set a} {B : Set b} {x y : A} (x≡y : x ≡ y) {u} → subst (\_ → B) x≡y u ≡ u
subst-const refl = refl
{-# REWRITE subst-const #-}

cong-id : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) → cong id x≡y ≡ x≡y
cong-id refl = refl

cong-trans : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y z : A} (x≡y : x ≡ y) (y≡z : y ≡ z)
           → cong f (trans x≡y y≡z) ≡ (trans (cong f x≡y) (cong f y≡z))
cong-trans f refl refl = refl
{-# REWRITE cong-trans #-}

cong-sym : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} (x≡y : x ≡ y) → cong f (sym x≡y) ≡ sym (cong f x≡y)
cong-sym f refl = refl
{-# REWRITE cong-sym #-}

--------------------------------------------------------------------------------
-- Dependent equality
--------------------------------------------------------------------------------

hsubst₂ : ∀ {a b c} {A : Set a} {B : A → Set b} (C : (x : A) → B x → Set c)
        → {x x' : A} (x≡x' : x ≡ x')
        → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
        → C x y → C x' y'
hsubst₂ C refl refl x = x

hsubst₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → (B x) → Set c} (D : (x : A) → (y : B x) → C x y → Set d)
        → {x x' : A} (x≡x' : x ≡ x')
        → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
        → {z : C x y} {z' : C x' y'} (z≡z' : hsubst₂ C x≡x' y≡y' z ≡ z')
        → D x y z → D x' y' z'
hsubst₃ D refl refl refl x = x

hsubst₃' : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : A → Set c} (D : (x : A) → (y : B x) → C x → Set d)
         → {x x' : A} (x≡x' : x ≡ x')
         → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
         → {z : C x} {z' : C x'} (z≡z' : subst C x≡x' z ≡ z')
         → D x y z → D x' y' z'
hsubst₃' D refl refl refl x = x

hcong : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y : A} → (x≡y : x ≡ y) → subst B x≡y (f x) ≡ f y
hcong f refl = refl

hcong₂' : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} (f : (x : A) → (y : B) → C x y) {x y : A} (x≡y : x ≡ y) {u v : B} (u≡v : u ≡ v) → subst₂ C x≡y u≡v (f x u) ≡ f y v
hcong₂' f refl refl = refl

hcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
       → (f : (x : A) → (y : B x) → C x y)
       → {x x' : A} (x≡x' : x ≡ x')
       → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
       → hsubst₂ C x≡x' y≡y' (f x y) ≡ f x' y'
hcong₂ f refl refl = refl

hcong₂'' : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
       → (f : (x : A) → (y : B x) → C)
       → {x x' : A} (x≡x' : x ≡ x')
       → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
       → f x y ≡ f x' y'
hcong₂'' f refl refl = refl

hcong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → (B x) → Set c} {D : (x : A) → (y : B x) → C x y → Set d}
       → (f : (x : A) → (y : B x) → (z : C x y) → D x y z)
       → {x x' : A} → (x≡x' : x ≡ x')
       → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
        → {z : C x y} {z' : C x' y'} (z≡z' : hsubst₂ C x≡x' y≡y' z ≡ z')
       → hsubst₃ D x≡x' y≡y' z≡z' (f x y z) ≡ f x' y' z'
hcong₃ f refl refl refl = refl

hcong₃' : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → (B x) → Set c} {D : Set d}
       → (f : (x : A) → (y : B x) → (z : C x y) → D)
       → {x x' : A} → (x≡x' : x ≡ x')
       → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
       → {z : C x y} {z' : C x' y'} (z≡z' : hsubst₂ C x≡x' y≡y' z ≡ z')
       → f x y z ≡ f x' y' z'
hcong₃' f refl refl refl = refl

hcong₃'' : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : A → Set c} {D : Set d}
       → (f : (x : A) → (y : B x) → (z : C x) → D)
       → {x x' : A} → (x≡x' : x ≡ x')
       → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
       → {z : C x} {z' : C x'} (z≡z' : subst C x≡x' z ≡ z')
       → f x y z ≡ f x' y' z'
hcong₃'' f refl refl refl = refl


hcong-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c} (f : (x : B) → C x) {x y : A} (g : A → B)
           → (x≡y : x ≡ y) → hcong f (cong g x≡y) ≡ hcong (f ∘ g) x≡y
hcong-cong f g refl = refl
{-# REWRITE hcong-cong #-}

subst-hcong : ∀ {a b c} {A : Set a} {B : Set b} (C : B → Set c) (f : A → B) {x y : A} (x≡y : x ≡ y) {u}
           → subst C (hcong f x≡y) u ≡ subst (C ∘ f) x≡y u
subst-hcong C f refl = refl
{-# REWRITE subst-hcong #-}

hcong-hcong : ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c} (f : (x : B) → C x) (g : A → B) {x y : A} (x≡y : x ≡ y)
           → hcong f (hcong g x≡y) ≡ hcong (f ∘ g) x≡y
hcong-hcong f g refl = refl
{-# REWRITE hcong-hcong #-}

subst₂-hcong₁ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} (D : B → C → Set d) (f : A → B)
                  {x y : A} (x≡y : x ≡ y) {p q : C} (p≡q : p ≡ q) {u}
              → subst₂ D (hcong f x≡y) p≡q u ≡ subst₂ (\u v → D (f u) v) x≡y p≡q u
subst₂-hcong₁ D f refl refl = refl
{-# REWRITE subst₂-hcong₁ #-}

subst-hcong₃'' : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : A → Set c} {D : Set d} (E : D → Set e)
               → (f : (x : A) → (y : B x) → (z : C x) → D)
               → {x x' : A} → (x≡x' : x ≡ x')
               → {y : B x} {y' : B x'} (y≡y' : subst B x≡x' y ≡ y')
               → {z : C x} {z' : C x'} (z≡z' : subst C x≡x' z ≡ z')
               → (u : E (f x y z))
               → subst E (hcong₃'' f x≡x' y≡y' z≡z') u ≡ hsubst₃' (\x y z → E (f x y z)) x≡x' y≡y' z≡z' u
subst-hcong₃'' E f refl refl refl u = refl
{-# REWRITE subst-hcong₃'' #-}

--------------------------------------------------------------------------------
-- Equality-utils
--------------------------------------------------------------------------------

subst-subst₂ : ∀ {a b} {A : Set a} (B : A → A → Set b) {x y} (x≡y : x ≡ y) z → subst (\u → B u u) x≡y z ≡ subst₂ B x≡y x≡y z
subst-subst₂ B refl z = refl

subst₂-≡ : ∀ {a} {A : Set a} {x y z w : A} → (x≡z : x ≡ z) → (y≡w : y ≡ w) → (x≡y : x ≡ y)
         → subst₂ _≡_ x≡z y≡w x≡y ≡ trans (trans (sym x≡z) x≡y) y≡w
subst₂-≡ refl refl refl = refl
{-# REWRITE subst₂-≡ #-}

subst-≡ : ∀ {a} {A : Set a} {x y : A} → (x≡x : x ≡ x) → (x≡y : x ≡ y)
         → subst (\x → x ≡ x) x≡y x≡x ≡ trans (trans (sym x≡y) x≡x) x≡y
subst-≡ x≡x x≡y = subst-subst₂ _≡_ x≡y x≡x
{-# REWRITE subst-≡ #-}



trans-sym-fun : ∀ {a} {A : Set a} (f : ∀ {x y : A} → x ≡ y → x ≡ y) {x y} (x≡y : x ≡ y)
              → trans (f x≡y) (sym (f refl)) ≡ x≡y
trans-sym-fun f refl = refl


subst-≡' : ∀ {a} {A : Set a} {x y : A} (f : A → A) → (x≡y : x ≡ y) → (fx≡x : f x ≡ x)
         → subst (\x → f x ≡ x) x≡y fx≡x ≡ trans (trans (sym (cong f x≡y)) fx≡x) x≡y
subst-≡' f refl fx≡x = refl

trans-comm-fun : ∀ {a} {A : Set a} {x y : A} (f : (x : A) → x ≡ x) (x≡y : x ≡ y)
               → trans (f x) x≡y ≡ trans x≡y (f y)
trans-comm-fun f refl = refl

untrans : ∀ {a} {A : Set a} {x y z : A} → {x≡y₁ x≡y₂ : x ≡ y} → (y≡z : y ≡ z) → trans x≡y₁ y≡z ≡ trans x≡y₂ y≡z → x≡y₁ ≡ x≡y₂
untrans {x≡y₁ = refl} refl y≡z = y≡z

trans-cong-comm-fun : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y}
                    → (f≡g : ∀ x → f x ≡ g x) (x≡y : x ≡ y)
                    → trans (cong f x≡y) (f≡g y) ≡ trans (f≡g x) (cong g x≡y)
trans-cong-comm-fun {x = x} f≡g refl = refl

cong-fun-id : ∀ {a} {A : Set a} {f : A → A} (f≡id : ∀ x → f x ≡ x) x
            → cong f (f≡id x) ≡ f≡id (f x)
cong-fun-id {f = f} f≡id x =
  untrans (f≡id x) (trans-cong-comm-fun f≡id (f≡id x) ⟨ trans ⟩
  cong (trans (f≡id (f x))) (cong-id (f≡id x)))


--------------------------------------------------------------------------------
-- Adjoint inverses, equivalences
--------------------------------------------------------------------------------

-- A proof of inverse that is always adjoint
adjoint-bw-fw : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A} → (∀ x → f (g x) ≡ x) → (∀ x → g (f x) ≡ x)
              → (∀ x → g (f x) ≡ x)
adjoint-bw-fw {f = f} {g = g} fg gf x =
  sym (cong (g ∘ f) (gf x)) ⟨ trans ⟩
  cong g (fg (f x)) ⟨ trans ⟩
  gf x

adjoint-bw-fw-adjoint : ∀ {a b} {A : Set a} {B : Set b} {f g} fg gf x
                        → cong g (fg x) ≡ adjoint-bw-fw {a} {b} {A} {B} {f} {g} fg gf (g x)
adjoint-bw-fw-adjoint {f = f} {g} fg gf x =
  begin
    cong g (fg x)
  ≡⟨ cong (\u → sym u ⟨ trans ⟩ gf (g (f (g x))) ⟨ trans ⟩ cong g (fg x)) (sym (cong-fun-id gf (g x))) ⟩
    (sym (cong (g ∘ f) (gf (g x))) ⟨ trans ⟩ gf (g (f (g x))) ⟨ trans ⟩ cong g (fg x))
  ≡⟨ cong (\u → sym (cong (g ∘ f) (gf (g x))) ⟨ trans ⟩ u) (sym (trans-cong-comm-fun (gf ∘ g) (fg x))) ⟩
    (sym (cong (g ∘ f) (gf (g x))) ⟨ trans ⟩ cong (g ∘ f ∘  g) (fg x) ⟨ trans ⟩ gf (g x))
  ≡⟨ cong (\u → sym (cong (g ∘ f) (gf (g x))) ⟨ trans ⟩ cong g u ⟨ trans ⟩ gf (g x)) (cong-fun-id fg x) ⟩
    (sym (cong (g ∘ f) (gf (g x))) ⟨ trans ⟩ cong g (fg (f (g x))) ⟨ trans ⟩ gf (g x))
  ∎

{-
sym-adjoint : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A} (fg : ∀ x → f (g x) ≡ x) (gf : ∀ x → g (f x) ≡ x)
            → (∀ x → cong g (fg x) ≡ gf (g x))
            → (∀ x → cong f (gf x) ≡ fg (f x))
sym-adjoint {f = f} {g = g} fg gf adj x =
  begin
    cong f (gf x)
  ≡⟨ {!cong (cong f) (sym (adj (f x)))!} ⟩
    {!cong f (gf (g (f x)))!}
  ≡⟨ {!!} ⟩
    {!cong (f ∘ g) (fg (f x)) ⟨ trans ⟩ fg (f x)!}
  ≡⟨ {!trans-cong-comm-fun adj!} ⟩
    fg (f x)
  ∎
-}