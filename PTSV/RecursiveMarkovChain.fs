module PTSV.RecursiveMarkovChain

open Utils
open PTSV.Global


type Node<'name> =
    | Entry of id:int
    | Call of id:int * box:'name
    | Internal of 'name
    | Exit of id:int
    | Return of id:int * box:'name
    
type Component<'name> when 'name : comparison =
    Component of
        entryAmount:int *
        exitAmount:int *
        nodes:Map<Node<'name>, (NumericType * Node<'name>) list> *
        // from box name to component name and interfaces
        boxMap:Map<'name, 'name * int * int>

type RecursiveMarkovChain<'name> when 'name : comparison =
    RecursiveMarkovChain of
        // the entry index with the component
        startingEntry:(int * 'name) *
        components:Map<'name, Component<'name>>

type PPDAState =
    | UsualState
    | SExit of id:int
    override x.ToString () =
        match x with
        | UsualState ->  "q"
        | SExit id   -> $"q{id}"

type PPDAGamma<'name> =
    | GNode of comp:'name * node:Node<'name>
    | GBox  of comp:'name * box:'name
    override x.ToString () =
        match x with
        | GNode (comp, node)    -> $"Node{{{comp}, {node}}}"
        | GBox  (comp, boxName) -> $"Box{{{comp}, {boxName}}}"

let initPPDAState = UsualState

let initPPDAGamma (RecursiveMarkovChain ((entryIdx, compName), _components)) =
    GNode (compName, Entry entryIdx)

let translateComponent
    compName
    (Component (_entryAmount, _exitAmount, nodes, boxMap)) =
    let retMapper retAmount boxName =
        [0..retAmount - 1]
        |> List.map (fun idx ->
            (SExit idx, GBox (compName, boxName), NUMERIC_ONE,
             UsualState, [
                 GNode (compName, Return (idx, boxName))
             ])) in
    let mapper node (p, newNode) = 
        let rec wrap st gs =
            [(UsualState, GNode (compName, node), p, st, gs)]
        if p = NUMERIC_ZERO then []
        else
            match newNode with
            | Entry id -> failwith $"Trying to go to entry point {id}."
            | Return (id, name) -> failwith $"Trying to go to return port {id} of Box \"{name}\"."
            | Call (entryId, boxName) ->
                let newCompName, _callAmount, _retAmount =
                    Map.find boxName boxMap in
                wrap UsualState [
                    GNode (newCompName, Entry entryId);
                    GBox (compName, boxName)
                ]
            | Exit id ->
                wrap (SExit id) []
            | inter ->
                wrap UsualState [GNode (compName, inter)] in
    let coreRules =
        // core rules from node rules
        Map.toSeq nodes
        |> Seq.map (fun (node, lst) ->
            List.map (mapper node) lst
            |> List.concat)
        |> Seq.toList
        |> List.concat
    in
    let boxRetRules =
        Map.toSeq boxMap
        |> Seq.map (fun (boxName, (_targetCompName, _callAmount, retAmount)) ->
            (retAmount, boxName))
        |> Seq.map (uncurry retMapper)
        |> Seq.toList
        |> List.concat
    in
    coreRules ++ boxRetRules

let rmcToPPDA (RecursiveMarkovChain ((_, _), components) as rmc) =
    ((initPPDAState, initPPDAGamma rmc),
     Map.toList components
     |> List.map (uncurry translateComponent)
     |> List.concat)
