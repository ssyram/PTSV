
/// this file is about statically infer HORS with product types
/// the `statically` here means every term is intrinsically non-polymorphic
/// but in some places, it can be any suitable type --
/// for example, when a parameter is not used, it can be of any type
/// any type is assume to have order-0 

module PTSV.StaticTypeInference

open System.Collections.Generic
open Utils

type Type<'id> =
    | TAny of 'id  // there is id for each any type
    | TBase
    | TFunc of Type<'id> * Type<'id>
    | TProd of Type<'id> list
    
type Term<'s> =
    | Sym of 's
    | App of Term<'s> * Term<'s>
    | Prod of Term<'s> list
    | Proj of uint * Term<'s>
    
type GenTypeConstraintsCtx<'s> = {
    genNextId : unit -> 's
}
    
/// \Gamma |- t : \tau
/// must mark each variable with a type
let rec genTypeConstraintsFromTerm ctx tyEnv term expTy =
    match term with
    | Sym s -> [(Map.find s tyEnv, expTy)]
    | App (t1, t2) ->
        let nextId = ctx.genNextId () in
        genTypeConstraintsFromTerm ctx tyEnv t1 (TFunc (TAny nextId, expTy)) ++
        genTypeConstraintsFromTerm ctx tyEnv t2 (TAny nextId)
    | Prod ts ->
        match expTy with
        | TAny _ ->
            let mapper t =
                let nextId = ctx.genNextId () in
                
            List.map
    
let rec occured ty =
    match ty with
    | TAny id -> Set.add id Set.empty
    | TBase -> Set.empty
    | TFunc (arg, ret) -> Set.union (occured arg) (occured ret)
    | TProd tys -> List.fold Set.union Set.empty $ List.map occured tys
    
exception UnifyTypePairException of msg:string
    
let rec unifyTypePair ty1 ty2 =
    match ty1, ty2 with
    | TAny id1, TAny id2 ->
        if id1 = id2 then
            []
        elif id1 < id2 then 
            [(id1, ty2)]
        else
            [(id2, ty1)]
    | TAny id, ty | ty, TAny id ->
        if Set.contains id $ occured ty then
            raise $ UnifyTypePairException $""
        [(id, ty)]
    | TBase, TBase -> []
    | TFunc (arg1, ret1), TFunc (arg2, ret2) ->
        unifyTypePair arg1 arg2 ++ unifyTypePair ret1 ret2
    | TProd tys1, TProd tys2 ->
        List.zip tys1 tys2
        |> List.map (uncurry unifyTypePair)
        |> List.concat
    | _ ->
        raise $ UnifyTypePairException $"Cannot unify: structure of \"{ty1}\" is different from \"{ty2}\""
        
