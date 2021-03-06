module Bob where

open import LTL.Stateless
open import LTL.Future
open import LTL.Causal
open import LTL.Product
open import LTL.Decoupled
open import LTL.CatHetSt
open import LTL.PolConsts


open import Prelude.Product
open import Prelude.Fin
open import Prelude.Vec
open import Prelude.Semiring
open import Prelude.Functor
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Nat.Properties
open import Data.These hiding ( map ) 

open import Agda.Primitive

open import Prelude.Sum renaming (Either to _⊎_)
open import Prelude.Empty
open import Prelude.Function

open import Def
open import Refine

data Fork : Set where
  fork51 : Fork
  fork12 : Fork
  fork23 : Fork
  fork34 : Fork
  fork45 : Fork
  

data Philosopher : Set where
  phil1 phil2 phil3 phil4 phil5 : Philosopher


data Availability (frk : Fork) : Set ʷ where
  unAv : ∀ {t} → Availability frk t
  av : ∀ {t} → Availability frk t


data IsAv {frk : Fork} : ⟦ Availability frk ⇒ ⟨ Set ⟩ ⟧ where
  isAv : ∀{t aval} → aval ≡ av {frk} {t} → IsAv aval


data IsUnAv {frk : Fork} : ⟦ Availability frk ⇒ ⟨ Set ⟩ ⟧ where
  isUnAv : ∀{t aval} → aval ≡ unAv {frk} {t} → IsUnAv aval


data Hunger (phil : Philosopher) : Set ʷ where
  hungry : ∀{t} → Hunger phil t  
  notHungry : ∀{t} → Hunger phil t  

data IsHungry {phil : Philosopher} : ⟦ Hunger phil ⇒ ⟨ Set ⟩ ⟧ where
  isHungry : ∀{t hungr} → hungr ≡ hungry {phil} {t} → IsHungry hungr


data IsNotHungry {phil : Philosopher} : ⟦ Hunger phil ⇒ ⟨ Set ⟩ ⟧ where
  isNotHungry : ∀{t hungr} → hungr ≡ notHungry {phil} {t} → IsNotHungry hungr

data ActionP (phil : Philosopher) : Set ʷ where
  eating : ∀{t} → ActionP phil t
  thinking : ∀{t} → ActionP phil t

data IsEating {phil : Philosopher} {frk1 frk2 : Fork} : ⟦ ActionP phil ⇒ ⟨ Set ⟩ ⟧ where
  isEating : ∀{t act} → act ≡ eating {phil} {t} → IsEating act

data IsThinking {phil : Philosopher} : ⟦ ActionP phil ⇒ ⟨ Set ⟩ ⟧ where
  isThinking : ∀{t act} → act ≡ thinking {phil} {t} → IsThinking act




eatWhileHungry : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ 
eatWhileHungry frk1 frk2 phil n
  = {av1 : Availability frk1 n} → {av2 : Availability frk2 n}
    → IsAv av1 → IsAv av2 →
        ((λ u → {hungr : Hunger phil u} → IsHungry hungr)
      ▻
        (λ u → Σ (Availability frk1 u) (λ av1 → Σ (Availability frk2 u) (λ av2 → Σ (ActionP phil u)
            (λ act → IsUnAv av1 × IsUnAv av2 × IsEating {_} {frk1} {frk2} act))))) n


stopEatingWhenNotHungry : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ
stopEatingWhenNotHungry frk1 frk2 phil n
  = {act : ActionP phil n} → IsEating {_} {frk1} {frk2} act → {hungr : Hunger phil n} → IsNotHungry hungr
    → ○ (λ u → Σ (Availability frk1 u) (λ av1 → Σ (Availability frk2 u)
          (λ av2 → IsAv av1 × IsAv av2))) n


thinkWhileNotHungry : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ
thinkWhileNotHungry frk1 frk2 phil
  =   (λ u → {hungr : Hunger phil u} → IsNotHungry hungr)
    ▻ 
      (λ u → Σ (ActionP phil u)
                 (λ act → IsThinking act))


eventuallyHungry : (phil : Philosopher) → Set ʷ
eventuallyHungry phil n
  = {hungr : Hunger phil n} → {act : ActionP phil n} → IsThinking act → IsNotHungry hungr
    → ◇ᶠ (λ u → Σ (Hunger phil u) (λ hungr → IsHungry hungr)) n


eventuallyNotHungry : (frk1 frk2 : Fork) (phil : Philosopher) → Set ʷ
eventuallyNotHungry frk1 frk2 phil n
  = {hungr : Hunger phil n} → {act : ActionP phil n} → IsEating {_} {frk1} {frk2} act → IsHungry hungr
    → ◇ᶠ (λ u → Σ (Hunger phil u) (λ hungr → IsNotHungry hungr)) n






-- 
-- eatWhenYouCan : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ 
-- eatWhenYouCan frk1 frk2 phil n
--   = {av1 : Availability frk1 n} → {av2 : Availability frk2 n} → {hungr : Hunger phil n}
--     → IsAv av1 → IsAv av2 → IsHungry hungr
--     → ○ (λ u → Σ (Availability frk1 u) (λ av1 → Σ (Availability frk2 u) (λ av2 → Σ (ActionP phil u)
--           (λ act → IsUnAv av1 × IsUnAv av2 × IsEating {_} {frk1} {frk2} act)))) n
-- 
-- 
-- stopEatingWhenNotHungry1 : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ
-- stopEatingWhenNotHungry1 frk1 frk2 phil n
--   = {hungr : Hunger phil n} → {act : ActionP phil n} → IsEating {_} {frk1} {frk2} act → IsNotHungry hungr
--      → ○ (λ u → Σ (Availability frk1 u) (λ av1 → Σ (Availability frk2 u) (λ av2 → Σ (ActionP phil u)
--            (λ act → IsAv av1 × IsAv av2 × IsThinking act)))) n
-- 
--

--- Version 2

-- We need to separate the conditions and the results and we need to be able to easily create refinement morphisms.
-- A single action is itself a system with a subset of the variables , thus we have a mapping.







-- 
-- F : ∀{α n} → {v : Vec (Set α) (suc n)} → Set α
-- F {α} {n} {v} = [ System v ⇒ ○ (System v) ]
-- 
-- 
-- 
-- 
-- action : ∀ {α n vars} → Action {α} {n} vars → Set α
-- action {_} {_} {vars} A = [ (System vars ∧ᵈ (cond A)) ⇒ᵈ ((○ (System vars) ∧↑ᵈ (resp A)) · fstsᵈ) ]
-- 
-- 









data Perit (n : Nat) : Set where
  per : ∀ {k} → k + k + (suc zero) ≡ n → Perit n

data Art (n : Nat) : Set where
  art : ∀ {k} → k + k ≡ n → Art n


vars : Vec Set 1
vars = Nat ∷ []

action1 : Action (Nat ∷ [])
cond action1 = ⟨ Perit ⟩
resp action1 = λ n ov nv → Art nv

action2 : Action (Nat ∷ [])
cond action2 = ⟨ Art ⟩
resp action2 = λ n ov nv → Perit nv

impl1 : Impl (action1 ∷ [])
impl1 n sys (yes x) = sys + sys , left (art {k = sys} refl) 
impl1 n sys (no x) = sys , (right refl)


impl2 : Impl (action2 ∷ [])
impl2 n .(k + k) (yes (art {k} refl)) = k + k + 1 , left (per {k = k} refl)
impl2 n sys (no x) = sys , right refl

spec : Spec vars
spec = action1 ∷ action2 ∷ []

impl : Impl spec
impl n sys (yes x , yes x₁) = {!!}
impl n sys (yes x , no x₁) = {!!}
impl n sys (no x , yes x₁) = {!!}
impl n sys (no x , no x₁) = {!!}




-- This needs to be replaced by a Type that returns a proof that some set is not fillable. (negation)
nThese : ∀{α n} → Vec (Set α) (suc n) → Set α
nThese (x ∷ []) = x
nThese (x ∷ y ∷ v) = These x (nThese (y ∷ v))

nTheseP : ∀{α β n} → (c : Vec (Set α) (suc n)) → Vec (Set β) (suc n) → nThese c → Set β
nTheseP (x ∷ []) (y ∷ []) q = y
nTheseP (x ∷ x₁ ∷ c) (y ∷ r) (this z) = y
nTheseP (x ∷ x₁ ∷ c) (y ∷ r) (that z) = nTheseP (x₁ ∷ c) r z
nTheseP (x ∷ x₁ ∷ c) (y ∷ r) (these z z₁) = y ⊎ nTheseP (x₁ ∷ c) r z₁

-- Do we need to Define "System vars" at all times (t) ?
-- I do not think that it is necessary.

bob : ∀{α n} → {vars : Vec (Set α) (suc n)}
    → ( cond : [ System vars ⇒ ⟨ Set α ⟩ ] )
    → ( resp : [ System vars ⇒ ○ (System vars) ⇒ ⟨ Set α ⟩ ] )
    → ( ncond : [ ○ (System vars) ⇒ ⟨ Set α ⟩ ] )
    → [ (System vars ∧ᵈ cond) ⇒ᵈ ((○ (System vars) ∧↑ᵈ resp) · fstsᵈ) ]
bob = {!!}




e : ∀{α n} → {v : Vec (Set α) (suc n)} → (f : [ System v ⇒ ○ (System v) ])
    → (reqc reqr : [ System v ⇒ ⟨ Set α ⟩ ]) → [ (reqc ⇒ₚ ○ reqr) $ʷ f ]
e = {!!}



-- re : ∀{n u} → Fin n
--      → Fin (n + u)
-- re zero = zero
-- re (suc f) = suc (re f)

-- tt : (n : Nat) → IsTrue (lessNat n (suc n))
-- tt zero = true
-- tt (suc n) = tt n

-- ge : ∀{n u} → Fin u
--      → Fin ((suc n) + u)
-- ge {n} {(suc u)} zero = re {n = suc n} (natToFin {n = (suc n)} n {{m<n = tt n}})
-- ge {n} {suc zero} (suc ())
-- ge {n} {suc (suc u)} (suc a) = transport (λ x → Fin (suc x)) (sym (add-suc-r n (suc u))) (Fin.suc (ge a))


-- tr : ∀{n u} → Fin (suc n)
--       → Fin (suc u) → Fin ((suc n) + (suc u))
-- tr zero b = {!!}
-- tr (suc zero) b = {!Fin.suc (tr a b)!}
-- tr (suc (suc a)) b = suc (tr (suc a) b)

-- mor : ∀{α n u m} → Vec ((Set α) ʷ) (suc n) → Vec ((Set α) ʷ) (suc u)
--       → Vec (Fin (suc n)) (suc m) → Vec ((Set α) ʷ) ((suc m) + (suc u))
-- mor {α} {n} v v2 vfn = (fmap′ (indexVec v) vfn) v++ v2
