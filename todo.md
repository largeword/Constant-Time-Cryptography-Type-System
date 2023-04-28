TODO:
1. define data structures:

  - environment
    Map Id TypeScheme

  - substitutions
    func
    - Subs = Map TypeVar Type
    - func : Subs -> Type -> Type
    - func : Subs -> TypeEnv -> TypeEnv

        TypeEnv -> TypeEnv
        Type -> Type

        subs a -> Int
        subs(array[a]) --> array[int]

  - functions / monad? for making new type var

  - 4 functions of Algorithm W
    - instatiate
    - generalize
    - U
    - W
