module Def where

open import LTL.Product public
open import LTL.Stateless public
open import LTL.CatHetSt public

open import Prelude.Vec public
open import Prelude.Product public
open import Prelude.Fin public
open import Prelude.Functor public
open import Prelude.Decidable public
open import Prelude.Empty public
open import Prelude.Sum renaming (Either to _⊎_) public

open import Agda.Primitive public



data Any {a b} {A : Set a} (P : A → Set b) : ∀{k} → Vec A k → Set (a ⊔ b) where
  instance
    zero : ∀ {k x xs} (p : P x) → Any P {suc k} (x ∷ xs)
    suc : ∀ {k x xs} (i : Any P {k} xs) → Any P {suc k} (x ∷ xs)

_∈v_ : ∀{a} → {A : Set a} → ∀{k} → A → Vec A k → Set a
a ∈v xs = Any (a ≡_) xs



System : ∀{α n} → Vec (Set α) (suc n) → (Set α) ʷ
System (x ∷ []) = ⟨ x ⟩
System (x ∷ y ∷ xs) = ⟨ x ⟩ ∧ System (y Vec.∷ xs)

-- Equality between times.

varsEq : ∀{α n t} → {vars : Vec (Set α) (suc n)} → (sys : System vars t) → (nsys : System vars (suc t)) → Set α
varsEq {vars = x ∷ []} sys nsys = sys ≡ nsys
varsEq {vars = x ∷ x₁ ∷ vars} (y , sys) (ny , nsys) = (y ≡ ny) × (varsEq {vars = x₁ ∷ vars} sys nsys)



pj : ∀{α n} → {vec : Vec (Set α) (suc n)} → (fn : Fin (suc n)) → [ System vec ⇒ ⟨ indexVec vec fn ⟩ ]
pj {_} {.0} {x ∷ []} zero = ids
pj {_} {.0} {x ∷ []} (suc ()) 
pj {_} {.(suc _)} {x ∷ y ∷ vec} zero = fsts
pj {_} {.(suc _)} {x ∷ y ∷ vec} (suc fn) = (pj fn) · snds


sys-proj : ∀{α n m} → {vecn : Vec (Set α) (suc n)}
           → (vfn : Vec (Fin (suc n)) (suc m)) → [ System vecn ⇒ System (fmap′ (indexVec vecn) vfn) ]
sys-proj (x ∷ []) = pj x
sys-proj (x ∷ y ∷ vfn) = boths $ʷ pj x $ʷ sys-proj (y ∷ vfn)




record Action {α n} (vars : Vec (Set α) (suc n)) : Set (lsuc α) where
  field
    cond : [ System vars ⇒ ⟨ Set α ⟩ ]
    resp : [ System vars ⇒ ○ (System vars) ⇒ ⟨ Set α ⟩ ]

open Action public


Spec : ∀ {α n k} → (vars : Vec (Set α) (suc n)) → Set (lsuc α)
Spec {_} {_} {k} vars = Vec (Action vars) (suc k)



Vdecide : ∀{α n} → Vec (Set α) (suc n) → Set α
Vdecide (x ∷ []) = Dec x
Vdecide (x ∷ x₁ ∷ xs) = Dec x × Vdecide (x₁ ∷ xs)


VdecideP : ∀{α n} → (c : Vec (Set α) (suc n)) → Vec (Set α) (suc n) → Vdecide c → Set α
VdecideP (x ∷ []) (y ∷ []) (yes z) = y 
VdecideP (x ∷ []) y (no z) = ⊥′
VdecideP (x ∷ x₁ ∷ c) (y ∷ ys) (yes z , zs) = y ⊎ (VdecideP (x₁ ∷ c) ys zs)
VdecideP (x ∷ x₁ ∷ c) (y ∷ ys) (no z , zs) = VdecideP (x₁ ∷ c) ys zs


--The implementation permits stuttering.

Impl : ∀{α n vars k} → Spec {α} {n} {k} vars → Set α 
Impl {_} {_} {vars} spec = let conds = fmap cond spec
                               resps = fmap resp spec
                           in  ∀ n → (sys : System vars n)
                               → let vc = fmap (λ f → f n sys) conds
                                     Ntc = Vdecide vc
                                 in (ntc : Ntc) → Σ (System vars (suc n)) λ nsys
                                    → let vr = fmap (λ f → f n sys nsys) resps
                                      in (VdecideP vc vr ntc) ⊎ varsEq {vars = vars} sys nsys
                                    


