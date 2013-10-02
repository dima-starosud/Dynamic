## Decidable TypeRep, Dynamic and Recursive instance search

Here is successful attempt to implement reasonable type representation.
Meanwhile new approach to mimic Haskell's type classes and do even more was developed.

Please see examples of usage in Test.agda.

### Decidable TypeRep

Main data type is following:

    data TypeRep [heterogeneous-type-ctors-vector] type

It has two parameters: vector of possible type constructors (Maybe, Int, Either, etc.) and represented type. There are two possible ways. Type "type" is one of type constructors from vector, or it is application of two types which also have type representation.
In this way one can easily define decidable function for two types which have type representation.

    decide : {t₁ t₂ : Set} → TypeRep vec t₁ → TypeRep vec t₂ → t₁ ≡ t₂ ⊎ t₁ ≢ t₂

### Recursive instance search approach

Recursive instance search doesn't work in Agda. But using type level computation we can simulate it. The main idea is to expand type of function in the way it will include all the necessary instance arguments. Also every new instance may contain additional requirements.
Let's say we want to create Show type class which will handle complex structures.
We have to do something like this:

    record Show (t : Set) : Set where  
      field get : t → String  

    ShowList : ∀ {a} → Instance (Show (List a))  
    ShowList {a} = instance [ Show a ] λ i → record {get = helper (Show.get i)}  
      where  
        helper : (a → String) → List a → String  
        helper show = _  

You can see that to define an instance we have to say what it requires and how to get exact instance if all the requirements provided.
