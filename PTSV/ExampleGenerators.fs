module PTSV.ExampleGenerators

// this file describes generation of 3 kinds of rPTSA examples
// the functions are not called else where
// one may call the three functions to generate rPTSA example to some scale

open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open Utils
open PTSV.Global

let private genHeader (k : uint) q0 m0 g0 =
    $"""
%%BEGIN rPTSA config
restriction := {k}
q0 := {q0}
m0 := {m0}
gamma0 := {g0}
%%END rPTSA config
    """

let private genRules k q0 m0 g0 (rules : string) =
    genHeader k q0 m0 g0 +
    "\n%BEGIN rPTSA rules\n" +
    $"{rules}" +
    "\n%END rPTSA rules"

type private State =
    | Q of string
    override x.ToString () =
        match x with
        | Q str -> str
type private Memory =
    | M of string
    override x.ToString () =
        match x with
        | M str -> str
type private Gamma =
    | G of string
    override x.ToString () =
        match x with
        | G str -> str
type private Probability =
    | P of string
    override x.ToString () =
        match x with
        | P str -> str
let private p obj =
    P $ toString obj
type private Operator =
    | OpUp of State * Memory * Gamma
    | OpDown of State * Memory
    | OpState of State
    | OpGenChar of string * State
    | OpTer
    | OpDiv
    override x.ToString () =
        match x with
        | OpUp (q', m', g') -> $"({q'}, {m'}, up {g'})"
        | OpDown (q', m') -> $"({q'}, {m'}, down)"
        | OpState q' -> $"{q'}"
        | OpGenChar (c, q) -> $"\"{c}\", {q}"
        | OpTer -> "\\top"
        | OpDiv -> "\\Omega"
    
type private PrimitiveOperator =
    | Up of Gamma
    | Down
type private PrimitiveTer = Ter
    
let private (--) p op =
    match p :> obj with
    | :? Probability as p -> (p, op)
    | :? string | :? NumericType | :? double | :? float as p -> (P $"{p}", op)
    | _ -> failwith $"Unknown type \"{p.GetType().Name}\" for Probability."
    
/// use to operate to chain the values
let private (=>) (q : State, m : Memory, g : Gamma) pOp =
    let one = P "1" in
    let p, op =
        match pOp :> obj with
        | :? State as q' -> one, OpState q'
        | :? (State * Memory * PrimitiveOperator) as (q', m', pOp) -> begin
            match pOp with
            | Up g -> one, OpUp (q', m', g)
            | Down -> one, OpDown (q', m')
            end
        | :? PrimitiveTer -> one, OpTer
        | :? (Probability * State) as (p, q') -> p, OpState q'
        | :? (Probability * (State * Memory * PrimitiveOperator)) as (p, (q', m', pOp)) -> begin
            match pOp with
            | Up g -> p, OpUp (q', m', g)
            | Down -> p, OpDown (q', m')
            end
        | :? (Probability * PrimitiveTer) as (p, _) -> p, OpTer
        | :? Operator as op -> one, op
        | :? (Probability * Operator) as (p, op) -> p, op
        | _ -> failwith "Operator Non-Supported."
    in
    (q, m, g, p, op)

let private up = Up
let private down = Down
let private genModelFromFormattedRules
        k
        (q0 : State)
        (m0 : Memory)
        (g0 : Gamma)
        (rules : (State * Memory * Gamma * Probability * Operator) list) =
    let rules =
        List.map toString rules
        |> String.concat "\n"
    in
    genRules k q0 m0 g0 rules

/// generate { a_1^na_2^n...a_k^n | n } example
///
/// 
/// Template:
/// 
/// // relay rules
/// (q{i + 1}, mi, g, (q{i + 1}, m_end_{i + 1}, up g))
/// (q_end_{i + 1}, m_end_{i + 1}, g, (q_end_{i + 1}, m{i + 1}, down))
/// // end point rule
/// (q{i + 1}, end_str, g, (q_end_{i + 1}, end_str, down))
/// // relay initial rules
/// (q1, m0, g, p, (q1, m_end_1, up g))
/// (q1, m0, g, 1 - p, (q_end_1, end_str, down))
/// // initial bottom rules
/// (q1, m0, root, p, (q1, m_end_1, up g))
/// (q1, m0, root, 1 - p, \top)
/// // bottom rules
/// (q_end_i, m_end_i, root, (q{i + 1}, m_end_{i + 1}, up g))
/// (q_end_k, m_end_k, root, \top)
let genKAgreement k =
    if k <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let qEnd idx = Q $"q_end_{idx}" in
    let root = G "root" in
    let p = P "p" in
    let one = P "1" in
    /// 1 - p
    let oneMP = P "1 - p" in
    let m idx = M $"m{idx}" in
    let mEnd idx = M $"m_end_{idx}" in
    let g = G "g" in
    let upG idx = OpUp (q idx, mEnd idx, g) in
    let endDown idx = OpDown (qEnd idx, m $ idx + 1) in
    let endStr = M "end_str" in
    let endStrDown idx = OpDown (qEnd idx, endStr) in
    let mapper idx =
        let relayRules =
            match idx with
            | 1 ->
                [
                    // bottom rules
                    (q 1, m 1, root, p, upG 1);
                    (q 1, m 1, root, oneMP, OpTer);
                    // initial relay rules
                    (q 1, m 1, g, p, upG 1);
                    (q 1, m 1, g, oneMP, endStrDown 1);
                    (qEnd 1, mEnd 1, g, one, endDown 1)
                ]
            | i ->
                [
                    (q i, m i, g, one, upG i)
                    (qEnd i, mEnd i, g, one, endDown i)
                    (q i, endStr, g, one, endStrDown i)
                ]
        in begin
            if idx = k then
                [ (qEnd k, mEnd k, root, one, OpTer) ]
            else
                [ (qEnd idx, mEnd idx, root, one, upG $ idx + 1) ]
        end ++ relayRules
    in
    [1..k]
    |> List.map (mapper >> List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint k) (q 1) (m 1) root
    
/// { w^n | w \in (a|b)* }
///
/// 
/// Template:
///
/// // initial bottom rules
/// (q1, mEmpty, root, pEnd, \top)
/// (q1, mEmpty, root, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, root, pB, (q1, mB_end_1, up g))
/// // initial relay rules
/// (q1, mEmpty, g, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, g, pB, (q1, mB_end_1, up g))
/// (q1, mEmpty, g, pEnd, (q_end_1, endStr, down))
/// // general down relay rules: i >= 1
/// (q_end_{i}, m{A|B}_end_{i}, g, 1, (q_end_{i}, m{A|B}_{i + 1}, down))
/// // intermediate relay rules
/// (q{i}, m{A|B}_{i}, g, 1, (q{i}, m{A|B}_end_{i}, up g))
/// (q{i}, endStr, g, 1, (q_end_{i}, endStr, down))
/// // intermediate bottom rule
/// (q_end_{i}, m{A|B}_end_{i}, root, 1, (q{i + 1}, m{A|B}_end_{i + 1}, up g))
/// // ending bottom rule
/// (q_end_n, m_{A|B}_end_n, root, 1, \top)
let genNCopy n =
    if n <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let mEmpty = M "mEmpty" in
    let root = G "root" in
    let pA = P "pA" in
    let pB = P "pB" in
    let pEnd = P "pEnd" in
    let g = G "g" in
    let qEnd idx = Q $"q_end_{idx}" in
    let mA idx = M $"mA_{idx}" in
    let mAEnd idx = M $"mA_end_{idx}" in
    let mB idx = M $"mB_{idx}" in
    let mBEnd idx = M $"mB_end_{idx}" in
    let endStr = M "endStr" in
    let one = P "1" in
    let mapper idx =
        let fillAB func =
            [
                func mA mAEnd;
                func mB mBEnd
            ]
        in
        let initAndIntermediateRules =
            match idx with
            | 1 ->
                [
                    // initial bottom rules
                    (q 1, mEmpty, root, pEnd, OpTer);
                    (q 1, mEmpty, root, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, root, pB, OpUp (q 1, mBEnd 1, g));
                    // initial relay rules
                    (q 1, mEmpty, g, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, g, pB, OpUp (q 1, mBEnd 1, g));
                    (q 1, mEmpty, g, pEnd, OpDown (qEnd 1, endStr))
                ]
            | i ->
                // intermediate relay rules
                [ (q i, endStr, g, one, OpDown (qEnd i, endStr)) ] ++
                fillAB (fun mX mXEnd ->
                    (q i, mX i, g, one, OpUp (q i, mXEnd i, g)))
        in
        initAndIntermediateRules ++
        // general down relay rules: i >= 1
        fillAB (fun mX mXEnd ->
            (qEnd idx, mXEnd idx, g, one, OpDown (qEnd idx, mX $ idx + 1))) ++
        if idx = n then
            // intermediate bottom rule: i >= 1 && i /= n
            fillAB (fun _mX mXEnd ->
                (qEnd n, mXEnd n, root, one, OpTer))
        else
            // ending bottom rule: i = n
            fillAB (fun _mX mXEnd ->
                (qEnd idx, mXEnd idx, root, one, OpUp (q $ idx + 1, mXEnd $ idx + 1, g)))
    in
    List.map mapper [1..n]
    |> List.map (List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint n) (q 1) mEmpty root


/// { a_1^n1...a_k^nkb_1^n1...b_k^nk | n1, ..., nk }
///
/// Template:
///
/// idea: the root does not keep the number, but just as a relay place
///
/// // first up
/// (q, m0, root, 1, (q, m_a_1, up g1))
/// (q, m0, g{i}, p, (q, cont, up g{i}))
/// (q, m0, g{i}, 1 - p, (q_end, endStr, down))
/// (q_end, cont, g{i}, 1, (q_end, cont, down))
/// // second up
/// (q, cont, g{i}, 1, (q, cont, up g{i}))
/// (q, endStr, g{i}, 1, (q_end, endStr, down))
/// // normal root relay
/// (q_end, m_{a|b}_{i}, root, 1, (q, m_{a|b}_{i + 1}, up g{i + 1}))
/// // end root relay 1
/// (q_end, m_a_k, root, 1, (q, m_b_1, up g1))
/// // end root relay 2
/// (q_end, m_b_k, root, 1, \top)
let genKCrossDependencies k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m0 = M "m0" in
    let root = G "root" in
    let g idx = G $"g{idx}" in
    let cont = M "cont" in
    let qEnd = Q "q_end" in
    let p = P "p" in
    let one = P "1" in
    let oneMP = P "1 - p" in
    let ma idx = M $"m_a_{idx}" in
    let mb idx = M $"m_b_{idx}" in
    let endStr = M "endStr" in
    /// the index is for g
    let mapper idx =
        [
            // first up
            (q, m0, g idx, p, OpUp (q, cont, g idx))
            (q, m0, g idx, oneMP, OpDown (qEnd, endStr))
            (qEnd, cont, g idx, one, OpDown (qEnd, cont))
            // second up
            (q, cont, g idx, one, OpUp (q, cont, g idx))
            (q, endStr, g idx, one, OpDown (qEnd, endStr))
        ] ++
        if idx = k then
            [
                // end root relay 1
                (qEnd, ma k, root, one, OpUp (q, mb 1, g 1))
                // end root relay 2
                (qEnd, mb k, root, one, OpTer)
            ]
        else
            [
                // normal root relay
                (qEnd, ma idx, root, one, OpUp (q, ma $ idx + 1, g $ idx + 1))
                (qEnd, mb idx, root, one, OpUp (q, mb $ idx + 1, g $ idx + 1))
            ]
    in
    let initialRule = (q, m0, root, one, OpUp (q, ma 1, g 1)) in
    List.map mapper [1..k]
    |> List.concat
    |> currying List.Cons initialRule
    |> List.map toString
    |> String.concat "\n"
    |> genRules 2u q m0 root


/// { w#...#w | w \in Dyck Language }
///
///
/// Idea
///
/// Use the tree-stack as a binary parsing tree
///
/// 
/// Template
///
/// // initial bottom rules
/// (q, m0, root, 1, (q, m2, up gL))  -- in order to have consistency, use root as simply the schedule center
///
/// // initial usual node
/// (q, m0, g{L|R}, p, (q, visited_left, up gL))  -- branching nodes
/// (q, m0, g{L|R}, 1 - p, (q, leaf, down))  -- leaf node
///
/// // bottom relay rules
/// (q, m{i}, root, 1, (q, m{i + 1}, up gL))  -- visit the stored tree for the i-th time
/// (q, m{k}, root, 1, \top)  -- end the visit
///
/// // middle relay rules
/// (q, to_revisit, g{L|R}, 1, (q, visited_left, up gL))  -- revisit, to visit left
/// (q, visited_left, g{L|R}, 1, (q, visited_right, up gR))
/// (q, visited_right, g{L|R}, 1, (q, to_revisit, down))
/// (q, leaf, g{L|R}, 1, (q, leaf, down))
let genKDyckLanguages prob k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m idx = M $"m{idx}" in
    let root = G "root" in
    let gL = G "gL" in
    let gR = G "gR" in  
    let p = P $"{prob}" in
    let one = P "1" in
    let oneMP = P $"1 - {prob}" in
    let visitedLeft = M "visited_left" in
    let visitedRight = M "visited_right" in
    let leaf = M "leaf" in
    let toRevisit = M "to_revisit" in
    let addLRRule func = [ func gL; func gR ] in
    let (|AtK|NotYet|) n = if n < k then NotYet else AtK in 
    let bottomRules =
        [1..k]
        |> List.map (function
            | AtK -> [ (q, m k, root, one, OpTer) ]
            | NotYet as idx -> [ (q, m idx, root, one, OpUp (q, m $ idx + 1, gL)) ])
        |> List.concat in
    (q, m 0, root, one, OpUp (q, m 1, gL)) :: bottomRules ++ List.concat (addLRRule $ fun g ->
        [
            // initial usual node
            (q, m 0, g, p, OpUp (q, visitedLeft, gL))
            (q, m 0, g, oneMP, OpDown (q, leaf))
            // middle relay rules
            (q, toRevisit, g, one, OpUp (q, visitedLeft, gL))
            (q, visitedLeft, g, one, OpUp (q, visitedRight, gR))
            (q, visitedRight, g, one, OpDown (q, toRevisit))
            (q, leaf, g, one, OpDown (q, leaf))
        ])
    |> List.map toString
    |> String.concat "\n"
    |> genRules (uint k) q (m 0) root
    
    
// example generators with shortcut

type ShortcutType = ShortcutTermination | ShortcutDivergence
    
/// generate { a_1^na_2^n...a_k^n | n } example
///
/// 
/// Template:
/// 
/// // relay rules
/// (q{i + 1}, mi, g, p, (q{i + 1}, m_end_{i + 1}, up g))
/// (q{i + 1}, mi, g, 1 - p, shortcut)
/// (q_end_{i + 1}, m_end_{i + 1}, g, 1, (q_end_{i + 1}, m{i + 1}, down))
/// // end point rule
/// (q{i + 1}, end_str, g, (q_end_{i + 1}, end_str, down))
/// // relay initial rules
/// (q1, m0, g, p, (q1, m_end_1, up g))
/// (q1, m0, g, 1 - p, (q_end_1, end_str, down))
/// // initial bottom rules
/// (q1, m0, root, p, (q1, m_end_1, up g))
/// (q1, m0, root, 1 - p, \top)
/// // bottom rules
/// (q_end_i, m_end_i, root, (q{i + 1}, m_end_{i + 1}, up g))
/// (q_end_k, m_end_k, root, \top)
let genKAgreementWithShortcut shortcutType k =
    if k <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let qEnd idx = Q $"q_end_{idx}" in
    let root = G "root" in
    let p = P "p" in
    let one = P "1" in
    /// 1 - p
    let oneMP = P "1 - p" in
    let m idx = M $"m{idx}" in
    let mEnd idx = M $"m_end_{idx}" in
    let g = G "g" in
    let upG idx = OpUp (q idx, mEnd idx, g) in
    let endDown idx = OpDown (qEnd idx, m $ idx + 1) in
    let endStr = M "end_str" in
    let endStrDown idx = OpDown (qEnd idx, endStr) in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let mapper idx =
        let relayRules =
            match idx with
            | 1 ->
                [
                    // bottom rules
                    (q 1, m 1, root, p, upG 1);
                    (q 1, m 1, root, oneMP, OpTer);
                    // initial relay rules
                    (q 1, m 1, g, p, upG 1);
                    (q 1, m 1, g, oneMP, endStrDown 1);
                    (qEnd 1, mEnd 1, g, one, endDown 1)
                ]
            | i ->
                [
                    (q i, m i, g, p, upG i);
                    (q i, m i, g, oneMP, shortcutOp);
                    (qEnd i, mEnd i, g, one, endDown i);
                    (q i, endStr, g, one, endStrDown i)
                ]
        in begin
            if idx = k then
                [ (qEnd k, mEnd k, root, one, OpTer) ]
            else
                [ (qEnd idx, mEnd idx, root, one, upG $ idx + 1) ]
        end ++ relayRules
    in
    [1..k]
    |> List.map (mapper >> List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint k) (q 1) (m 1) root
    
/// { w^n | w \in (a|b)* }
///
/// 
/// Template:
///
/// // initial bottom rules
/// (q1, mEmpty, root, pEnd, \top)
/// (q1, mEmpty, root, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, root, pB, (q1, mB_end_1, up g))
/// // initial relay rules
/// (q1, mEmpty, g, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, g, pB, (q1, mB_end_1, up g))
/// (q1, mEmpty, g, pEnd, (q_end_1, endStr, down))
/// // general down relay rules: i >= 1
/// (q_end_{i}, m{A|B}_end_{i}, g, 1, (q_end_{i}, m{A|B}_{i + 1}, down))
/// // intermediate relay rules
/// (q{i}, m{A|B}_{i}, g, pA + pB, (q{i}, m{A|B}_end_{i}, up g))
/// (q{i}, m{A|B}_{i}, g, pEnd, shortcutOp)
/// (q{i}, endStr, g, 1, (q_end_{i}, endStr, down))
/// // intermediate bottom rule
/// (q_end_{i}, m{A|B}_end_{i}, root, 1, (q{i + 1}, m{A|B}_end_{i + 1}, up g))
/// // ending bottom rule
/// (q_end_n, m_{A|B}_end_n, root, 1, \top)
let genNCopyWithShortcut shortcutType n =
    if n <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let mEmpty = M "mEmpty" in
    let root = G "root" in
    let pA = P "pA" in
    let pB = P "pB" in
    let pEnd = P "pEnd" in
    let g = G "g" in
    let qEnd idx = Q $"q_end_{idx}" in
    let mA idx = M $"mA_{idx}" in
    let mAEnd idx = M $"mA_end_{idx}" in
    let mB idx = M $"mB_{idx}" in
    let mBEnd idx = M $"mB_end_{idx}" in
    let endStr = M "endStr" in
    let one = P "1" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let mapper idx =
        let fillAB func =
            [
                func mA mAEnd;
                func mB mBEnd
            ]
        in
        let initAndIntermediateRules =
            match idx with
            | 1 ->
                [
                    // initial bottom rules
                    (q 1, mEmpty, root, pEnd, OpTer);
                    (q 1, mEmpty, root, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, root, pB, OpUp (q 1, mBEnd 1, g));
                    // initial relay rules
                    (q 1, mEmpty, g, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, g, pB, OpUp (q 1, mBEnd 1, g));
                    (q 1, mEmpty, g, pEnd, OpDown (qEnd 1, endStr))
                ]
            | i ->
                // intermediate relay rules
                [ (q i, endStr, g, one, OpDown (qEnd i, endStr)) ] ++
                List.concat (fillAB (fun mX mXEnd ->
                    [(q i, mX i, g, P "pA + pB", OpUp (q i, mXEnd i, g));
                     (q i, mX i, g, pEnd, shortcutOp)]))
        in
        initAndIntermediateRules ++
        // general down relay rules: i >= 1
        fillAB (fun mX mXEnd ->
            (qEnd idx, mXEnd idx, g, one, OpDown (qEnd idx, mX $ idx + 1))) ++
        if idx = n then
            // intermediate bottom rule: i >= 1 && i /= n
            fillAB (fun _mX mXEnd ->
                (qEnd n, mXEnd n, root, one, OpTer))
        else
            // ending bottom rule: i = n
            fillAB (fun _mX mXEnd ->
                (qEnd idx, mXEnd idx, root, one, OpUp (q $ idx + 1, mXEnd $ idx + 1, g)))
    in
    List.map mapper [1..n]
    |> List.map (List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint n) (q 1) mEmpty root


/// { a_1^n1...a_k^nkb_1^n1...b_k^nk | n1, ..., nk }
///
/// Template:
///
/// idea: the root does not keep the number, but just as a relay place
///
/// // first up
/// (q, m0, root, 1, (q, m_a_1, up g1))
/// (q, m0, g{i}, p, (q, cont, up g{i}))
/// (q, m0, g{i}, 1 - p, (q_end, endStr, down))
/// (q_end, cont, g{i}, 1, (q_end, cont, down))
/// // second up
/// (q, cont, g{i}, p, (q, cont, up g{i}))
/// (q, cont, g{i}, 1 - p, shortcutOp)
/// (q, endStr, g{i}, 1, (q_end, endStr, down))
/// // normal root relay
/// (q_end, m_{a|b}_{i}, root, 1, (q, m_{a|b}_{i + 1}, up g{i + 1}))
/// // end root relay 1
/// (q_end, m_a_k, root, 1, (q, m_b_1, up g1))
/// // end root relay 2
/// (q_end, m_b_k, root, 1, \top)
let genKCrossDependenciesWithShortcut shortcutType k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m0 = M "m0" in
    let root = G "root" in
    let g idx = G $"g{idx}" in
    let cont = M "cont" in
    let qEnd = Q "q_end" in
    let p = P "p" in
    let one = P "1" in
    let oneMP = P "1 - p" in
    let ma idx = M $"m_a_{idx}" in
    let mb idx = M $"m_b_{idx}" in
    let endStr = M "endStr" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    /// the index is for g
    let mapper idx =
        [
            // first up
            (q, m0, g idx, p, OpUp (q, cont, g idx));
            (q, m0, g idx, oneMP, OpDown (qEnd, endStr));
            (qEnd, cont, g idx, one, OpDown (qEnd, cont));
            // second up
            (q, cont, g idx, p, OpUp (q, cont, g idx));
            (q, cont, g idx, oneMP, shortcutOp);
            (q, endStr, g idx, one, OpDown (qEnd, endStr))
        ] ++
        if idx = k then
            [
                // end root relay 1
                (qEnd, ma k, root, one, OpUp (q, mb 1, g 1));
                // end root relay 2
                (qEnd, mb k, root, one, OpTer)
            ]
        else
            [
                // normal root relay
                (qEnd, ma idx, root, one, OpUp (q, ma $ idx + 1, g $ idx + 1))
                (qEnd, mb idx, root, one, OpUp (q, mb $ idx + 1, g $ idx + 1))
            ]
    in
    let initialRule = (q, m0, root, one, OpUp (q, ma 1, g 1)) in
    List.map mapper [1..k]
    |> List.concat
    |> currying List.Cons initialRule
    |> List.map toString
    |> String.concat "\n"
    |> genRules 2u q m0 root


/// { w#...#w | w \in Dyck Language }
///
///
/// Idea
///
/// Use the tree-stack as a binary parsing tree
///
/// 
/// Template
///
/// // initial bottom rules
/// (q, m0, root, 1, (q, m2, up gL))  -- in order to have consistency, use root as simply the schedule center
///
/// // initial usual node
/// (q, m0, g{L|R}, p, (q, visited_left, up gL))  -- branching nodes
/// (q, m0, g{L|R}, 1 - p, (q, leaf, down))  -- leaf node
///
/// // bottom relay rules
/// (q, m{i}, root, 1, (q, m{i + 1}, up gL))  -- visit the stored tree for the i-th time
/// (q, m{k}, root, 1, \top)  -- end the visit
///
/// // middle relay rules
/// (q, to_revisit, g{L|R}, p, (q, visited_right, up gL))  -- revisit, to visit left
/// (q, to_revisit, g{L|R}, 1 - p, (q, visited_right, up gR))
/// (q, visited_left, g{L|R}, 1, (q, visited_right, up gR))
/// (q, visited_right, g{L|R}, 1, (q, to_revisit, down))
/// (q, leaf, g{L|R}, 1, (q, leaf, down))
let genKDyckLanguagesWithRandomUp prob k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m idx = M $"m{idx}" in
    let root = G "root" in
    let gL = G "gL" in
    let gR = G "gR" in  
    let p = P $"{prob}" in
    let one = P "1" in
    let oneMP = P $"1 - {prob}" in
    let visitedLeft = M "visited_left" in
    let visitedRight = M "visited_right" in
    let leaf = M "leaf" in
    let toRevisit = M "to_revisit" in
    let addLRRule func = [ func gL; func gR ] in
    let (|AtK|NotYet|) n = if n < k then NotYet else AtK in 
    let bottomRules =
        [1..k]
        |> List.map (function
            | AtK -> [ (q, m k, root, one, OpTer) ]
            | NotYet as idx -> [ (q, m idx, root, one, OpUp (q, m $ idx + 1, gL)) ])
        |> List.concat in
    (q, m 0, root, one, OpUp (q, m 1, gL)) :: bottomRules ++ List.concat (addLRRule $ fun g ->
        [
            // initial usual node
            (q, m 0, g, p, OpUp (q, visitedLeft, gL))
            (q, m 0, g, oneMP, OpDown (q, leaf))
            // middle relay rules
            (q, toRevisit, g, p, OpUp (q, visitedRight, gL))
            (q, toRevisit, g, oneMP, OpUp (q, visitedRight, gR))
            (q, visitedLeft, g, one, OpUp (q, visitedRight, gR))
            (q, visitedRight, g, one, OpDown (q, toRevisit))
            (q, leaf, g, one, OpDown (q, leaf))
        ])
    |> List.map toString
    |> String.concat "\n"
    |> genRules (uint k) q (m 0) root

/// { w^n | w \in (a|b)* }
///
/// 
/// Template:
///
/// // initial bottom rules
/// (q1, mEmpty, root, pEnd, \top)
/// (q1, mEmpty, root, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, root, pB, (q1, mB_end_1, up g))
/// // initial relay rules
/// (q1, mEmpty, g, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, g, pB, (q1, mB_end_1, up g))
/// (q1, mEmpty, g, pEnd, (q_end_1, endStr, down))
/// // general down relay rules: i >= 1
/// (q_end_{i}, m{A|B}_end_{i}, g, 1, (q_end_{i}, m{A|B}_{i + 1}, down))
/// // intermediate relay rules
/// (q{i}, m{A|B}_{i}, g, i/(i + 1), (q{i}, m{A|B}_end_{i}, up g))
/// (q{i}, m{A|B}_{i}, g, 1/(i + 1), shortcutOp)
/// (q{i}, endStr, g, 1, (q_end_{i}, endStr, down))
/// (q_end_ins, m{A|B}_end_{i}, g, 1, shortcutOp)
/// // intermediate bottom rule
/// (q_end_{i}, m{A|B}_end_{i}, root, 1, (q{i + 1}, m{A|B}_end_{i + 1}, up g))
/// (q_end_ins, m{A|B}_end_{i}, root, 1, \top)
/// // ending bottom rule
/// (q_end_n, m_{A|B}_end_n, root, 1, \top)
/// (q_end_ins, m{A|B}_end_{i}, root, 1, \top)
let genNCopyWithVariantShortcut shortcutType n =
    if n <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let qInstantEnd = Q "q_instant_end" in
    let mEmpty = M "mEmpty" in
    let root = G "root" in
    let pA = P "pA" in
    let pB = P "pB" in
    let pEnd = P "pEnd" in
    let g = G "g" in
    let qEnd idx = Q $"q_end_{idx}" in
    let mA idx = M $"mA_{idx}" in
    let mAEnd idx = M $"mA_end_{idx}" in
    let mB idx = M $"mB_{idx}" in
    let mBEnd idx = M $"mB_end_{idx}" in
    let endStr = M "endStr" in
    let one = P "1" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpDown (qInstantEnd, mEmpty)
        | ShortcutDivergence  -> OpDiv
    in
    let mapper idx =
        let fillAB func =
            [
                func mA mAEnd;
                func mB mBEnd
            ]
        in
        let initAndIntermediateRules =
            match idx with
            | 1 ->
                [
                    // initial bottom rules
                    (q 1, mEmpty, root, pEnd, OpTer);
                    (q 1, mEmpty, root, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, root, pB, OpUp (q 1, mBEnd 1, g));
                    // initial relay rules
                    (q 1, mEmpty, g, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, g, pB, OpUp (q 1, mBEnd 1, g));
                    (q 1, mEmpty, g, pEnd, OpDown (qEnd 1, endStr))
                ]
            | i ->
                // intermediate relay rules
                [ (q i, endStr, g, one, OpDown (qEnd i, endStr)) ] ++
                List.concat (fillAB (fun mX mXEnd ->
                    [
                        (q i, mX i, g, P $"{i} / {i + 1}", OpUp (q i, mXEnd i, g))
                        (q i, mX i, g, P $"1 / {i + 1}"  , shortcutOp)
                    ]))
        in
        initAndIntermediateRules ++
        // general down relay rules: i >= 1
        List.concat (fillAB (fun mX mXEnd ->
            [
                (qEnd idx, mXEnd idx, g, one, OpDown (qEnd idx, mX $ idx + 1))
                (qInstantEnd, mXEnd idx, g, one, shortcutOp)
                (qInstantEnd, mXEnd idx, root, one, OpTer)
            ])) ++
        if idx = n then
            // intermediate bottom rule: i >= 1 && i /= n
            fillAB (fun _mX mXEnd ->
                (qEnd n, mXEnd n, root, one, OpTer))
        else
            // ending bottom rule: i = n
            fillAB (fun _mX mXEnd ->
                (qEnd idx, mXEnd idx, root, one, OpUp (q $ idx + 1, mXEnd $ idx + 1, g)))
    in
    List.map mapper [1..n]
    |> List.map (List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint n) (q 1) mEmpty root
    
    

/// { a_1^n1...a_k^nkb_1^n1...b_k^nk | n1, ..., nk }
///
/// Template:
///
/// idea: the root does not keep the number, but just as a relay place
///
/// // first up
/// (q, m0, root, 1, (q, m_a_1, up g1))
/// (q, m0, g{i}, p, (q, cont, up g{i}))
/// (q, m0, g{i}, 1 - p, (q_end, endStr, down))
/// (q_end, cont, g{i}, 1, (q_end, cont, down))
/// // second up
/// (q, cont, g{i}, i / i + 1, (q, cont, up g{i}))
/// (q, cont, g{i}, 1 / i + 1, shortcutOp)
/// (q, endStr, g{i}, 1, (q_end, endStr, down))
/// // normal root relay
/// (q_end, m_{a|b}_{i}, root, 1, (q, m_{a|b}_{i + 1}, up g{i + 1}))
/// (q_end_ins, m_{a|b}_{i}, root, 1, \top)
/// // end root relay 1
/// (q_end, m_a_k, root, 1, (q, m_b_1, up g1))
/// // end root relay 2
/// (q_end, m_b_k, root, 1, \top)
let genKCrossDependenciesWithVariantShortcut prob shortcutType k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m0 = M "m0" in
    let root = G "root" in
    let g idx = G $"g{idx}" in
    let cont = M "cont" in
    let qEnd = Q "q_end" in
    let p = P $"{prob}" in
    let one = P "1" in
    let oneMP = P $"1 - {prob}" in
    let ma idx = M $"m_a_{idx}" in
    let mb idx = M $"m_b_{idx}" in
    let endStr = M "endStr" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpDown (qEnd, cont)
        | ShortcutDivergence  -> OpDiv
    in
    /// the index is for g
    let mapper idx =
        [
            // first up
            (q, m0, g idx, p, OpUp (q, cont, g idx));
            (q, m0, g idx, oneMP, OpDown (qEnd, endStr));
            (qEnd, cont, g idx, one, OpDown (qEnd, cont));
            // second up
            (q, cont, g idx, P $"{idx} / {idx + 1}", OpUp (q, cont, g idx));
            (q, cont, g idx, P $"1 / {idx + 1}", shortcutOp);
            (q, endStr, g idx, one, OpDown (qEnd, endStr))
            // this will duplicate the above in Ter case and meaningless in Div case 
//            (qEnd, cont, g idx, one, shortcutOp)
        ] ++
//        [
//            (qEnd, ma idx, root, one, OpTer)
//            (qEnd, mb idx, root, one, OpTer)
//        ] ++
        if idx = k then
            [
                // end root relay 1
                (qEnd, ma k, root, one, OpUp (q, mb 1, g 1));
                // end root relay 2
                (qEnd, mb k, root, one, OpTer)
            ]
        else
            [
                // normal root relay
                (qEnd, ma idx, root, one, OpUp (q, ma $ idx + 1, g $ idx + 1))
                (qEnd, mb idx, root, one, OpUp (q, mb $ idx + 1, g $ idx + 1))
            ]
    in
    let initialRule = (q, m0, root, one, OpUp (q, ma 1, g 1)) in
    List.map mapper [1..k]
    |> List.concat
    |> currying List.Cons initialRule
    |> List.map toString
    |> String.concat "\n"
    |> genRules 2u q m0 root
    
    
/// { w^n | w \in (a|b)* }
///
/// 
/// Template:
///
/// // initial bottom rules
/// (q1, mEmpty, root, pEnd, \top)
/// (q1, mEmpty, root, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, root, pB, (q1, mB_end_1, up g))
/// // initial relay rules
/// (q1, mEmpty, g, pA, (q1, mA_end_1, up g))
/// (q1, mEmpty, g, pB, (q1, mB_end_1, up g))
/// (q1, mEmpty, g, pEnd, (q_end_1, endStr, down))
/// // general down relay rules: i >= 1
/// (q_end_{i}, m{A|B}_end_{i}, g, 1, (q_end_{i}, m{A|B}_{i + 1}, down))
/// // intermediate relay rules
/// (q{i}, m{A|B}_{i}, g, 1, (q{i}, m{A|B}_end_{i}, up g))
/// (q{i}, endStr, g, 1, (q_end_{i}, endStr, down))
/// // intermediate bottom rule
/// (q_end_{i}, m{A|B}_end_{i}, root, i / (i + 1), (q{i + 1}, m{A|B}_end_{i + 1}, up g))
/// (q_end_{i}, m{A|B}_end_{i}, root, 1 / (i + 1), shortcutOp)
/// // ending bottom rule
/// (q_end_n, m_{A|B}_end_n, root, 1, \top)
let genNCopyWithBottomVariantShortcut shortcutType n =
    if n <= 0 then "" else
    let q idx = Q $"q{idx}" in
    let mEmpty = M "mEmpty" in
    let root = G "root" in
    let pA = P "pA" in
    let pB = P "pB" in
    let pEnd = P "pEnd" in
    let g = G "g" in
    let qEnd idx = Q $"q_end_{idx}" in
    let mA idx = M $"mA_{idx}" in
    let mAEnd idx = M $"mA_end_{idx}" in
    let mB idx = M $"mB_{idx}" in
    let mBEnd idx = M $"mB_end_{idx}" in
    let endStr = M "endStr" in
    let one = P "1" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let mapper idx =
        let fillAB func =
            [
                func mA mAEnd;
                func mB mBEnd
            ]
        in
        let initAndIntermediateRules =
            match idx with
            | 1 ->
                [
                    // initial bottom rules
                    (q 1, mEmpty, root, pEnd, OpTer);
                    (q 1, mEmpty, root, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, root, pB, OpUp (q 1, mBEnd 1, g));
                    // initial relay rules
                    (q 1, mEmpty, g, pA, OpUp (q 1, mAEnd 1, g));
                    (q 1, mEmpty, g, pB, OpUp (q 1, mBEnd 1, g));
                    (q 1, mEmpty, g, pEnd, OpDown (qEnd 1, endStr))
                ]
            | i ->
                // intermediate relay rules
                [ (q i, endStr, g, one, OpDown (qEnd i, endStr)) ] ++
                List.concat (fillAB (fun mX mXEnd ->
                    [
                        (q i, mX i, g, one, OpUp (q i, mXEnd i, g))
                    ]))
        in
        initAndIntermediateRules ++
        // general down relay rules: i >= 1
        List.concat (fillAB (fun mX mXEnd ->
            [
                (qEnd idx, mXEnd idx, g, one, OpDown (qEnd idx, mX $ idx + 1))
            ])) ++
        if idx = n then
            // intermediate bottom rule: i >= 1 && i /= n
            fillAB (fun _mX mXEnd ->
                (qEnd n, mXEnd n, root, one, OpTer))
        else
            // ending bottom rule: i = n
            List.concat $ fillAB (fun _mX mXEnd ->
                [
                    (qEnd idx, mXEnd idx, root, P $"{idx} / {idx + 1}", OpUp (q $ idx + 1, mXEnd $ idx + 1, g))
                    (qEnd idx, mXEnd idx, root, P $"1 / {idx + 1}", shortcutOp)
                ])
    in
    List.map mapper [1..n]
    |> List.map (List.map toString >> String.concat "\n")
    |> String.concat "\n"
    |> genRules (uint n) (q 1) mEmpty root
    
    
/// { w#...#w | w \in Dyck Language }
///
///
/// Idea
///
/// Use the tree-stack as a binary parsing tree
///
/// 
/// Template
///
/// // initial bottom rules
/// (q, m0, root, 1, (q, m2, up gL))  -- in order to have consistency, use root as simply the schedule center
///
/// // initial usual node
/// (q, m0, g{L|R}, p, (q, visited_left, up gL))  -- branching nodes
/// (q, m0, g{L|R}, 1 - p, (q, leaf, down))  -- leaf node
///
/// // bottom relay rules
/// (q, m{i}, root, 1, (q, m{i + 1}, up gL))  -- visit the stored tree for the i-th time
/// (q, m{k}, root, 1, \top)  -- end the visit
///
/// // middle relay rules
/// (q, to_revisit, g{L|R}, p, (q, visited_left, up gL))  -- revisit, to visit left
/// (q, to_revisit, g{L|R}, 1 - p, shortcutOp)
/// (q, visited_left, g{L|R}, 1, (q, visited_right, up gR))
/// (q, visited_right, g{L|R}, 1, (q, to_revisit, down))
/// (q, leaf, g{L|R}, 1, (q, leaf, down))
let genKDyckLanguagesWithShortcut prob shortcutType k =
    if k <= 0 then "" else
    let q = Q "q" in
    let m idx = M $"m{idx}" in
    let root = G "root" in
    let gL = G "gL" in
    let gR = G "gR" in  
    let p = P $"{prob}" in
    let one = P "1" in
    let oneMP = P $"1 - {prob}" in
    let visitedLeft = M "visited_left" in
    let visitedRight = M "visited_right" in
    let leaf = M "leaf" in
    let toRevisit = M "to_revisit" in
    let addLRRule func = [ func gL; func gR ] in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let (|AtK|NotYet|) n = if n < k then NotYet else AtK in 
    let bottomRules =
        [1..k]
        |> List.map (function
            | AtK -> [ (q, m k, root, one, OpTer) ]
            | NotYet as idx -> [ (q, m idx, root, one, OpUp (q, m $ idx + 1, gL)) ])
        |> List.concat in
    (q, m 0, root, one, OpUp (q, m 1, gL)) :: bottomRules ++ List.concat (addLRRule $ fun g ->
        [
            // initial usual node
            (q, m 0, g) => p -- (q, visitedLeft, up gL)
            (q, m 0, g) => oneMP -- (q, leaf, down)
            // middle relay rules
            (q, toRevisit, g) => p -- (q, visitedLeft, up gL)
            (q, toRevisit, g) => oneMP -- shortcutOp
            (q, visitedLeft, g) => (q, visitedRight, up gR)
            (q, visitedRight, g) => (q, toRevisit, down)
            (q, leaf, g) => (q, leaf, down)
        ])
    |> List.map toString
    |> String.concat "\n"
    |> genRules (uint k) q (m 0) root

/// example:
/// x = 100
/// y = 0
/// 
/// while x - y > 2:
///     y = y + 1 @ 1/3; y + 2 @ 1/3; y + 3
/// 
/// while y > 9:
///     y = y @ 1/3; y - 10
/// - initialise the value of `x`:
/// (qX0, m0, root) -> (qX0, m0, up loop)
/// - 0 <= i <= 9:
/// (qX{i}, m0, loop) -> (qX{i + 1}, mLower, up loop)
/// - 10 <= i <= 97:
/// (qX{i}, m0, loop) -> (qX{i + 1}, mUsual, up loop)
/// - 98 <= i <= 99:
/// (qX{i}, m0, loop) -> (qX{i + 1}, mReached, up loop)
/// (qX100, m0, loop) -> (qBack, mReached, down)
/// 
/// - get back to start `y`:
/// (qBack, {All M}, loop) -> (qBack, {Original M}, down)
/// - start `y`:
/// (qBack, m0, root) -> (YL1_0, m0, up loop)
/// - run first loop (L1) for `y`:
/// (YL1_0, {All M but mReached}, loop) 
///   ->(1/3) (YL1_0, {Original M}, up loop)
///   ->(1/3) (YL1_1, {Original M}, up loop)
///   ->(1/3) (YL1_2, {Original M}, up loop)
/// - relay rules for `y`: 0 < i <= 2
/// (YL1_{i}, {All M}, loop) -> (YL1_{i - 1}, {Original M}, up loop)
/// - reached, end the first loop for `y`:
/// (YL1_0, mReached, loop) -> YL2_0
/// - start getting into the second loop for `y`:
/// (YL2_0, {All M but m Lower}, loop)
///   ->(1/3) YL2_0
///   ->(2/3) (YL2_9, m0, down)
/// - relay rules: 0 < i <= 9
/// (YL2_{i}, {All M}, loop) -> (YL2_{i - 1}, m0, down)
/// - reached lower, end the second loop for `y`:
/// (YL2_0, mReached, loop) -> (qEnd, m0, down)
/// - terminate at the bottom
/// (qEnd, m0, root) -> \top
let genAmber_SequentialLoops _ =
    let qX i = Q $"qX{i}" in
    let m0 = M "m0" in
    let mReached = M "mReached" in
    let mLower = M "mLower" in
    let mUsual = M "mUsual" in
    let mEnd = M "mEnd" in
    let root = G "root" in
    let loop = G "loop" in
    let qEnd = Q "qEnd" in
    let qBack = Q "qBack" in
    let oneThird = P "1/3" in
    let twoThird = P "2/3" in
    let yL1 i = Q $"YL1_{i}" in
    let yL2 i = Q $"YL2_{i}" in
    // - initialise the value of `x`:
    // (qX0, m0, root) -> (qX0, m0, up loop)
    // - start `y`:
    // (qBack, m0, root) -> (YL1_0, m0, up loop)
    // - terminate at the bottom
    // (qEnd, m0, root) -> \top
    let rootRules =
        [
            (qX 0, m0, root) => (qX 0, m0, Up loop)
            (qBack, m0, root) => (yL1 0, m0, Up loop)
            (qEnd, m0, root) => Ter
        ]
    in
    // initialise `x`
    // - 0 <= i <= 9:
    // (qX{i}, m0, loop) -> (qX{i + 1}, mLower, up loop)
    // - 10 <= i <= 97:
    // (qX{i}, m0, loop) -> (qX{i + 1}, mUsual, up loop)
    // - 98 <= i <= 99:
    // (qX{i}, m0, loop) -> (qX{i + 1}, mReached, up loop)
    // (qX100, m0, loop) -> (qBack, mReached, down)
    let initialiseX =
        flip List.map [0..100] $ fun i ->
            match i with
            | i when 0 <= i && i <= 9 ->
                (qX i, m0, loop) => (qX $ i + 1, mLower, Up loop)
            | i when 10 <= i && i <= 97 ->
                (qX i, m0, loop) => (qX $ i + 1, mUsual, Up loop)
            | 98 | 99 ->
                (qX i, m0, loop) => (qX $ i + 1, mReached, Up loop)
            | 100 ->
                (qX 100, m0, loop) => (qBack, mReached, Down)
            | _ -> IMPOSSIBLE ()
    in
    // - get back to start `y`:
    // (qBack, {All M}, loop) -> (qBack, {Original M}, down)
    let backToStartY =
        flip List.map [mReached; mUsual; mLower] $ fun m ->
            (qBack, m, loop) => (qBack, m, Down)
    in
    // - run first loop (L1) for `y`:
    // (YL1_0, {All M but mReached}, loop) 
    //   ->(1/3) (YL1_0, {Original M}, up loop)
    //   ->(1/3) (YL1_1, {Original M}, up loop)
    //   ->(1/3) (YL1_2, {Original M}, up loop)
    let firstLoopForY =
        Seq.toList $ seq {
            for yi in [0..2] do
                for m in [mLower; mUsual] do
                    yield (yL1 0, m, loop) => oneThird -- (yL1 yi, m, Up loop)
        }
    in
    // - relay rules for `y`: 0 < i <= 2
    // (YL1_{i}, {All M}, loop) -> (YL1_{i - 1}, {Original M}, up loop)
    let relayForY =
        Seq.toList $ seq {
            for yi in [1..2] do
                for m in [mLower; mUsual; mReached] do
                    yield (yL1 yi, m, loop) => (yL1 $ yi - 1, m, Up loop)
        }
    in
    // - relay rules: 0 < i <= 9
    // (YL2_{i}, {All M}, loop) -> (YL2_{i - 1}, mEnd, down)
    let yRelayRules =
        Seq.toList $ seq {
            for i in [1..9] do
                for m in [mReached; mUsual; mLower] do
                    yield (yL2 i, m, loop) => (yL2 $ i - 1, mEnd, Down)
        }
    in
    // - reached, end the first loop for `y`:
    // (YL1_0, mReached, loop) -> YL2_0
    // - start getting into the second loop for `y`:
    // (YL2_0, {All M but m Lower}, loop)
    //   ->(1/3) YL2_0
    //   ->(2/3) (YL2_9, mEnd, down)
    // - reached lower, end the second loop for `y`:
    // (YL2_0, mReached, loop) -> (qEnd, mEnd, down)
    let otherYRules =
        [
            (yL1 0, mReached, loop) => yL2 0
            (yL2 0, mLower, loop) => (qEnd, mEnd, Down)
            (qEnd, mLower, loop) => (qEnd, mEnd, Down)
        ] ++
        List.concat (flip List.map [mReached; mUsual] $ fun m ->
            [ (yL2 0, m, loop) => oneThird -- yL2 0
              (yL2 0, m, loop) => twoThird -- (yL2 9, mEnd, Down) ])
    in
    let allRules =
        [ rootRules
          initialiseX
          backToStartY
          firstLoopForY
          relayForY
          yRelayRules
          otherYRules ]
        |> List.concat
        |> List.map toString
        |> String.concat "\n"
    in
    genRules (uint 2) (qX 0) m0 root allRules

let doList lst flatMap =
    List.concat $ List.map flatMap lst

/// x = -100
/// y = 0
/// while x < 0:
///     x = x + 1 @ 1/10; x
///     while y >= 100:
///         y = y - 100 @ 1/2; y - 90
///     y = y + 1000
///
/// We first get Up to the top (100-level)
/// Then, we get to the Y top -- the target is to back to X at
/// each level and then to the bottom
/// So the restriction is `1`.
///
/// -- root is still the relay place
/// (qX1, m0, root) => (qX1, m0, Up X)
/// (qDownX, m0, root) => \top
/// -- at first, every X is created, and then try to get down
/// 0 <= i <= 99
/// (qX{i}, m0, X) => (qX{i + 1}, m0, Up X)
/// (qX100, m0, X) => qDownX
/// -- Then, for every `qDownX`, we have the rules to try to see Y
/// -- Note that as it is possible to have rules to loop
/// -- It is important to have a proxy X so that the loop is conducted in proxy
/// (qDownX, m0, [proxy]X) =>
///     1/10 -- (qY00, m0, Up Y)
///     9/10 -- (qY00, mCont, Up Y)
/// 0 <= i <= 9
/// (qDownY{i}0, m0, [proxy]X) => (qDownX, m0, Down)
/// (qDownY{i}0, mCont, [proxy]X) => (qDownX, mEnd, Up proxyX)
/// -- End the proxy
/// (qDownX, mEnd, [proxy]X) => (qDownX, mEnd, Down)
/// -- For each Y, we firstly create it and then get down again
/// -- to save place, we use every `10` for a step
/// 0 <= i <= 99
/// (qY{i}0, m0, Y) => (qY{i + 1}0, m0, Up Y)
/// (qY1000, m0, Y) => qDownY00
/// (qDownY00, m0, Y) =>
///     1/2 -- (qDownY80, m0, Down)
///     1/2 -- (qDownY90, m0, Down)
/// 1 <= i <= 9
/// (qDownY{i}0, m0, Y) => (qDownY{i - 1}0, m0, Down)
let genAmber_NestedLoops _ =
    let qX i = Q $"qX{i}" in
    let qDownX = Q "qDownX" in
    let qY_0 i = Q $"qY{i}0" in
    let qDownY_0 i = Q $"qDownY{i}0" in
    let m0 = M "m0" in
    let mCont = M "mCont" in
    let mEnd = M "mEnd" in
    let root = G "root" in
    let X = G "X" in
    let proxyX = G "proxyX" in
    let Y = G "Y" in
    let oneHalf = P "1/2" in
    let oneTenth = P "1/10" in
    let nineTenth = P "9/10" in
    let rules =
        // -- root is still the relay place
        [
            (qX 1, m0, root) => (qX 1, m0, Up X)
            (qDownX, m0, root) => Ter
        ] ++
        // -- at first, every X is created, and then try to get down
        // 0 <= i <= 99
        flip List.map [0..99] (fun i ->
            (qX i, m0, X) => (qX $ i + 1, m0, Up X)) ++
        [
            (qX 100, m0, X) => qDownX
            // -- Then, for every `qDownX`, we have the rules to Y
            (qDownX, m0, X) => oneTenth -- (qY_0 0, m0, Up Y)
            (qDownX, m0, X) => nineTenth -- (qY_0 0, mCont, Up Y)
            // copy to proxy
            (qDownX, m0, proxyX) => oneTenth -- (qY_0 0, m0, Up Y)
            (qDownX, m0, proxyX) => nineTenth -- (qY_0 0, mCont, Up Y)
        ] ++
        // 0 <= i <= 9
        doList [0..9] (fun i ->
            [
                (qDownY_0 i, m0, X) => (qDownX, m0, Down)
                (qDownY_0 i, mCont, X) => (qDownX, mEnd, Up proxyX)
                // copy to proxy
                (qDownY_0 i, m0, proxyX) => (qDownX, m0, Down)
                (qDownY_0 i, mCont, proxyX) => (qDownX, mEnd, Up proxyX)
            ]) ++
        [
            // End the [proxy]X
            (qDownX, mEnd, X) => (qDownX, mEnd, Down)
            (qDownX, mEnd, proxyX) => (qDownX, mEnd, Down)
        ] ++
        // -- For each Y, we firstly create it and then get down again
        // -- to save place, we use every `10` for a step
        // 0 <= i <= 99
        flip List.map [0..99] (fun i ->
            (qY_0 i, m0, Y) => (qY_0 $ i + 1, m0, Up Y)) ++
        [
            (qY_0 100, m0, Y) => qDownY_0 0
            (qDownY_0 0, m0, Y) => oneHalf -- (qDownY_0 8, m0, Down)
            (qDownY_0 0, m0, Y) => oneHalf -- (qDownY_0 9, m0, Down)
        ] ++
        // 1 <= i <= 9
        flip List.map [1..9] (fun i ->
            (qDownY_0 i, m0, Y) => (qDownY_0 $ i - 1, m0, Down))
    in
    let rules =
        rules
        |> List.map toString
        |> String.concat "\n"
    in
    genRules (uint 1) (qX 1) m0 root rules

/// { true }
/// x = 0;
/// y = 0;
/// t = 0;
/// while (x + 3 <= 50 && t <= 150) {
///     if (y <= 49) {
///         prob {
///             0.5 : y = y + 1; t = t + 1;
///             0.5 : y = y; t = t + 1;
///         }
///     }
///     else {
///         prob {
///             0.25 : x = x; t = t + 1;
///             0.25 : x = x + 1; t = t + 1;
///             0.25 : x = x + 2; t = t + 1;
///             0.25 : x = x + 3; t = t + 1;
///         }
///     }
/// }
/// { t <= 150 }
/// Initialise the limit -- tLimit, then back to work on the two values again
/// qI0, m0, root -> qI0, m0, up count
/// 
/// 0 <= i <= tLimit:
///     qI{i}, m0, count -> qI{i + 1}, mCont, up count
/// 
/// qI{tLimit + 1}, m0, count -> qBack, mEnd , down
/// qBack, mCont, count -> qBack, mCont, down
/// qBack, m0, root -> qY0, mEnd, up count
///
/// 0 <= i <= 49:
///     qY{i}, mCont, count ->
///         0.5 -- qY{i}, mCont, up count
///         0.5 -- qY{i + 1}, mCont, up count
///     qY{i}, mEnd, count -> qBack, mEnd, down
/// 
/// qY50, mCont, count -> qX0
///
/// 0 <= i <= 47:
///     qX{i}, mCont, count ->
///         0.25 -- qX{i}, mCont, up count
///         0.25 -- qX{i + 1}, mCont, up count
///         0.25 -- qX{i + 2}, mCont, up count
///         0.25 -- qX{i + 3}, mCont, up count
///     qX{i}, mEnd, count -> qBack, mEnd, down
/// 
/// qX{48, 49, 50}, mCont, count -> Div  // may be ignored
/// qX{48, 49, 50}, mEnd, count -> qBack, mEnd, down
/// qBack, mEnd, root -> Ter
let genPrspeed tLimit =
    let qI i = Q $"qI{i}" in
    let m0 = M "m0" in
    let count = G "count" in
    let root = G "root" in
    let qBack = Q "qBack" in
    let mCont = M "mCont" in
    let qY i = Q $"qY{i}" in
    let mEnd = M "mEnd" in
    let qX i = Q $"qX{i}" in
    let rules =
        // qI0, m0, root -> qI0, m0, up count
        [(qI 0, m0, root) => (qI 0, m0, up count)] ++
        // 0 <= i <= tLimit:
        //     qI{i}, m0, count -> qI{i + 1}, mCont, up count
        flip List.map [0..tLimit] (fun i ->
            (qI i, m0, count) => (qI $ i + 1, mCont, up count)) ++
        // qI{tLimit + 1}, m0, count -> qBack, mEnd , down
        // qBack, mCont, count -> qBack, mCount, down
        // qBack, m0, root -> qY0, m0, up count
        [
            (qI $ tLimit + 1, m0, count) => (qBack, mEnd, down)
            (qBack, mCont, count) => (qBack, mCont, down)
            (qBack, m0, root) => (qY 0, mEnd, up count)
        ] ++
        // 0 <= i <= 49:
        //     qY{i}, mCont, count ->
        //         0.5 -- qY{i}, mCont, up count
        //         0.5 -- qY{i + 1}, mCont, up count
        //     qY{i}, mEnd, count -> qBack, mEnd, down
        List.concat (flip List.map [0..49] $ fun i ->
            [
                (qY i, mCont, count) => p 0.5 -- (qY i, mCont, up count)
                (qY i, mCont, count) => p 0.5 -- (qY $ i + 1, mCont, up count)
                (qY i, mEnd,  count) => (qBack, mEnd, down)
            ]) ++
        // qY50, mCont, count -> qX0
        [ (qY 50, mCont, count) => qX 0 ] ++
        // 0 <= i <= 47:
        //     qX{i}, mCont, count ->
        //         0.25 -- qX{i}, mCont, up count
        //         0.25 -- qX{i + 1}, mCont, up count
        //         0.25 -- qX{i + 2}, mCont, up count
        //         0.25 -- qX{i + 3}, mCont, up count
        //     qX{i}, mEnd, count -> qBack, mEnd, down
        List.concat (flip List.map [0..47] $ fun i ->
            [
                (qX i, mCont, count) => p 0.25 -- (qX i, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 1, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 2, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 3, mCont, up count)
                (qX i, mEnd,  count) => (qBack, mEnd, down)
            ]) ++
        // qX{48, 49, 50}, mCount, count -> Div  // may be ignored
        // qX{48, 49, 50}, mEnd,   count -> qBack, mEnd, down
        flip List.map [48..50] (fun i ->
            (qX i, mEnd, count) => (qBack, mEnd, down)) ++
        // qEnd, mEnd, root -> Ter
        [
            (qBack, mEnd, root) => Ter
        ]
    in
    genModelFromFormattedRules (uint 2) (qI 0) m0 root rules


/// { true }
/// x = xStart
/// y = 0
/// while (x <= 99 && y <= 99) {
///     x = x + 1
///     prob {
///         0.5 : y = y + 2
///         0.5 : y = y
///     }
/// }
/// { x >= 100 }
///
/// The idea of the rules: make the rest of the x path as the stack and let y to pursue x
/// x{xStart}, m0, root -> x{xStart}, m0, up track
/// xStart <= i <= 99:
///     x{i}, m0, track -> x{i + 1}, onTrack, up track
/// x100, m0, track -> qBack, raceEnd, down
/// qBack, onTrack, track -> qBack, onTrack, down
/// qBack, m0, root -> y0, m0, up track
/// 0 <= i <= 99:
///     y{i}, onTrack, track ->
///         0.5 -- y{i + 1}, onTrack, up track
///         0.5 -- y{i}, onTrack, up track
///     y{i}, raceEnd, track -> Div  // the turtle has reached the end and the race ends
/// y100, {onTrack, raceEnd}, track -> win, raceEnd, down
/// win, onTrack, track -> win, raceEnd, down
/// win, m0, root -> Ter
let genFullRace xStart =
    let x i = Q $"x{i}" in
    let m0  = M "m0" in
    let track = G "track" in
    let root = G "root" in
    let onTrack = M "onTrack" in
    let qBack = Q "qBack" in
    let y i = Q $"y{i}" in
    let raceEnd = M "raceEnd" in
    let win = Q "win" in
    let rules =
        // x{xStart}, m0, root -> x{xStart}, m0, up track
        [ (x xStart, m0, root) => (x xStart, m0, up track) ] ++
        // xStart <= i <= 99:
        //     x{i}, m0, track -> x{i + 1}, onTrack, up track
        flip List.map [xStart..99] (fun i ->
            (x i, m0, track) => (x $ i + 1, onTrack, up track)) ++
        // x100, m0, track -> qBack, raceEnd, down
        // qBack, onTrack, track -> qBack, onTrack, down
        // qBack, m0, root -> y0, m0, up track
        [
            (x 100, m0, track)      => (qBack, raceEnd, down)
            (qBack, onTrack, track) => (qBack, onTrack, down)
            (qBack, m0, root)       => (y 0, m0, up track)
        ] ++
        // 0 <= i <= 99:
        //     y{i}, onTrack, track ->
        //         0.5 -- y{i + 1}, onTrack, up track
        //         0.5 -- y{i}, onTrack, up track
        //     y{i}, raceEnd, track -> Div  // the turtle has reached the end and the race ends
        List.concat (flip List.map [0..2..98] $ fun i ->
            [
                (y i, onTrack, track) => p 0.5 -- (y $ i + 2, onTrack, up track)
                (y i, onTrack, track) => p 0.5 -- (y i, onTrack, up track)
            ]) ++
        // y100, {onTrack, raceEnd}, track -> win, raceEnd, down
        // win, onTrack, track -> win, raceEnd, down
        // win, m0, root -> Ter
        [
            (y 100, onTrack, track) => (win, raceEnd, down)
            (win, onTrack, track)   => (win, raceEnd, down)
            (win, m0, root)         => Ter
        ]
    in
    genModelFromFormattedRules (uint 2) (x xStart) m0 root rules


/// ONLY THE TP CAN BE COMPUTED AND THE ETT COMPUTATION IS TOO LARGE
/// ALSO, TP IS THE VIOLATION PROBABILITY, WHICH IS WHAT WE NEED, ETT IS MEANINGLESS
/// { true }
/// x = 0;
/// t = 0;
/// while (x <= 99 && t <= 600) {
///     t = t + 1;
///     prob {
///         0.75 : x = x + 1;
///         0.25 : x = x - 1;
///     }
/// }
/// { t <= 600 }
///
/// The idea behind: create a counter to get to and then see the number of {x}
/// t0, m0, root -> t0, m0, up count
///
/// 0 <= i <= tCount:
///     t{i}, m0, count -> t{i + 1}, cont, up count
///
/// t{tCount + 1}, m0, count -> xBack, end, down
/// xBack, cont, count -> xBack, cont, down
/// xBack, m0, root -> x0, m0, up count
///
/// -tCount-1 <= i <= 99:
///     x{i}, cont, count ->
///         0.75 -- x{i + 1}, cont, up count
///         0.25 -- x{i - 1}, cont, up count
///     x{i}, end, count -> toTer, end, down
/// x100, {cont, end}, count -> Div  // may ignore
///
/// toTer, cont, count -> toTer, end, down
/// toTer, m0, root -> Ter
let genFullRdWalk tCount =
    let t i =
        if i < 0 then Q $"t_{abs i}"
        else Q $"t{i}"
    in
    let x i = 
        if i < 0 then Q $"x_{abs i}"
        else Q $"x{i}"
    in
    let m0  = M "m0" in
    let root = G "root" in
    let mEnd = M "end" in
    let count = G "count" in
    let getDown = Q "getDown" in
    let cont = M "cont" in
    let rules =
        // t0, m0, root -> t0, m0, up count
        [ (t 0, m0, root) => (t 0, m0, up count) ] ++
        // 0 <= i <= tCount:
        //     t{i}, m0, count -> t{i + 1}, cont, up count
        flip List.map [0..tCount] (fun i ->
            (t i, m0, count) => (t $ i + 1, cont, up count)) ++
        // t{tCount + 1}, m0, count -> getDown, end, down
        // getDown, cont, count -> getDown, cont, down
        // getDown, m0, root -> x0, mEnd, up count
        [
            (t $ tCount + 1, m0, count) => (getDown, mEnd, down)
            (getDown, cont, count) => (getDown, cont, down)
            (getDown, m0, root) => (x 0, mEnd, up count)
        ] ++
        // -tCount-1 <= i <= 99:
        //     x{i}, cont, count ->
        //         0.75 -- x{i + 1}, cont, up count
        //         0.25 -- x{i - 1}, cont, up count
        //     x{i}, end, count -> getDown, end, down
        List.concat (flip List.map [-tCount-1..99] $ fun i ->
            [
                (x i, cont, count) => p 0.75 -- (x $ i + 1, cont, up count)
                (x i, cont, count) => p 0.25 -- (x $ i - 1, cont, up count)
                (x i, mEnd, count) => (getDown, mEnd, down)
            ]) ++
        // x100, {cont, end}, count -> Div  // may ignore
        //
        // getDown, m0, root -> Ter
        [
            (getDown, mEnd, root) => Ter
        ]
    in
    genModelFromFormattedRules (uint 2) (t 0) m0 root rules


/// { true }
/// i = 0;
/// t = 0;
/// while (i < 5 && t <= tSize) {
///     t = t + 1;
///     if (i == 0) {
///         i = i + 1;
///     }
///     else if (i == 1) {
///         prob {
///             0.8 : i = i + 1;
///             0.2 : i = i;
///         }
///     }
///     else if (i == 2) {
///         prob {
///             0.6 : i = i + 1;
///             0.4 : i = i;
///         }
///     }
///     else if (i == 3) {
///         prob {
///             0.4 : i = i + 1;
///             0.6 : i = i;
///         }
///     }
///     else if (i == 4) {
///         prob {
///             0.2 : i = i + 1;
///             0.8 : i = i;
///         }
///     }
/// }
/// { t <= tSize }
///
/// The t counter is again placed on the tree stack
/// t0, m0, root -> t0, m0, up count
///
/// 0 <= i <= tSize:
/// t{i}, m0, count -> t{i + 1}, cont, up count
///
/// t{tSize + 1}, m0, count -> back, toEnd, down
/// back, cont, count -> back, cont, down
/// back, m0, root -> i0, toEnd, up count
///
/// i0, cont, count -> i1, cont, up count
/// i1, cont, count ->
///     0.8 -- i2, cont, up count
///     0.2 -- i1, cont, up count
/// i2, cont, count ->
///     0.6 -- i3, cont, up count
///     0.4 -- i2, cont, up count
/// i3, cont, count ->
///     0.4 -- i4, cont, up count
///     0.6 -- i3, cont, up count
/// i4, cont, count ->
///     0.2 -- i5, cont, up count
///     0.8 -- i4, cont, up count
/// i5, cont, count -> Div  // may be ignored
///
/// 0 <= i <= 4:
/// i{i}, toEnd, count -> back, toEnd, down
///
/// Additionally:
/// i5, toEnd, count -> back, toEnd, down
///
/// back, toEnd, root -> Ter
let genFullCoupon tSize =
    let t i = Q $"t{i}" in
    let i i = Q $"i{i}" in
    let m0  = M "m0" in
    let root = G "root" in
    let toEnd = M "toEnd" in
    let count = G "count" in
    let back = Q "back" in
    let cont = M "cont" in
    let rules =
        // t0, m0, root -> t0, m0, up count
        [ (t 0, m0, root) => (t 0, m0, up count) ] ++ 
        // 0 <= i <= tSize:
        // t{i}, m0, count -> t{i + 1}, cont, up count
        flip List.map [0..tSize] (fun i ->
            (t i, m0, count) => (t $ i + 1, cont, up count)) ++
        // t{tSize + 1}, m0, count -> back, toEnd, down
        // back, cont, count -> back, cont, down
        // back, m0, root -> i0, toEnd, up count
        [
            (t $ tSize + 1, m0, count) => (back, toEnd, down)
            (back, cont, count) => (back, cont, down)
            (back, m0, root) => (i 0, toEnd, up count)
        ] ++
        // i0, cont, count -> i1, cont, up count
        // i1, cont, count ->
        //     0.8 -- i2, cont, up count
        //     0.2 -- i1, cont, up count
        // i2, cont, count ->
        //     0.6 -- i3, cont, up count
        //     0.4 -- i2, cont, up count
        // i3, cont, count ->
        //     0.4 -- i4, cont, up count
        //     0.6 -- i3, cont, up count
        // i4, cont, count ->
        //     0.2 -- i5, cont, up count
        //     0.8 -- i4, cont, up count
        // i5, cont, count -> Div  // may be ignored
        // 
        // 0 <= i <= 4:
        // i{i}, toEnd, count -> back, toEnd, down
        [ (i 0, cont, count) => (i 1, cont, up count) ] ++
        List.concat (flip List.map [1..4] $ fun idx ->
            [
                // to exactly work with the number
                (i idx, cont, count) => p $"0.{(10 - 2 * idx)}" -- (i $ idx + 1, cont, up count)
                (i idx, cont, count) => p $"0.{(2 * idx)}"      -- (i idx, cont, up count)
                (i idx, toEnd, count) => (back, toEnd, down)
            ]) ++
        // Additionally:
        // i5, toEnd, count -> back, toEnd, down
        [ (i 5, toEnd, count) => (back, toEnd, down) ] ++ 
        // back, toEnd, root -> Ter
        [ (back, toEnd, root) => Ter ]
    in
    genModelFromFormattedRules (uint 2) (t 0) m0 root rules


/// { true }
/// x = 0;
/// i = 0;
/// while (x <= xLimit && i <= 500) {
///     i = i + 1;
///     prob {
///         0.5 : x = x + 1;
///         0.5 : x = x;
///     }
/// }
/// { i <= 500 }
///
/// Again, let i be the counter and x be the adder to reach it.
///
/// i0, m0, root -> i0, m0, up count
///
/// 0 <= i <= 500:
/// i{i}, m0, count -> i{i + 1}, cont, up count
///
/// i501, m0, count -> qBack, mEnd, down
/// qBack, cont, count -> qBack, cont, down
/// qBack, m0, root -> x0, mEnd, up count
///
/// 0 <= i <= xLimit:
/// x{i}, cont, count ->
///     0.5 -- x{i + 1}, cont, up count
///     0.5 -- x{i},     cont, up count
/// x{i}, mEnd, count -> qBack, mEnd, down
/// 
///
/// x{xLimit + 1}, cont, count -> Div  // may be ignored
/// x{xLimit + 1}, mEnd, count -> qBack, mEnd, down
/// qBack, mEnd, root -> Ter
let genRdAdder xLimit =
    let i i = Q $"i{i}" in
    let x i = Q $"x{i}" in
    let m0  = M "m0" in
    let root = G "root" in
    let mEnd = M "mEnd" in
    let count = G "count" in
    let qBack = Q "qBack" in
    let cont = M "cont" in
    let rules =
        [
            // i0, m0, root -> i0, m0, up count
            [
                (i 0, m0, root) => (i 0, m0, up count)
            ]
            // 0 <= i <= 500:
            // i{i}, m0, count -> i{i + 1}, cont, up count
            flip List.map [0..500] (fun idx ->
                (i idx, m0, count) => (i $ idx + 1, cont, up count))
            // i501, m0, count -> qBack, mEnd, down
            // qBack, cont, count -> qBack, cont, down
            // qBack, m0, root -> x0, mEnd, up count
            [
                (i 501, m0, count) => (qBack, mEnd, down)
                (qBack, cont, count) => (qBack, cont, down)
                (qBack, m0, root) => (x 0, mEnd, up count)
            ]
            // 0 <= i <= xLimit:
            // x{i}, cont, count ->
            //     0.5 -- x{i + 1}, cont, up count
            //     0.5 -- x{i},     cont, up count
            // x{i}, mEnd, count -> qBack, mEnd, down
            List.concat (flip List.map [0..xLimit] $ fun i ->
                [
                    (x i, cont, count) => p 0.5 -- (x $ i + 1, cont, up count)
                    (x i, cont, count) => p 0.5 -- (x i,       cont, up count)
                    (x i, mEnd, count) => (qBack, mEnd, down)
                ])
            // x{xLimit + 1}, cont, count -> Div  // may be ignored
            // x{xLimit + 1}, mEnd, count -> qBack, mEnd, down
            // qBack, mEnd, root -> Ter
            [
                (x $ xLimit + 1, mEnd, count) => (qBack, mEnd, down)
                (qBack, mEnd, root) => Ter
            ]
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint 2) (i 0) m0 root rules
    

/// The tool example -- the true example inside, other than the example written on paper
/// { true }
/// x = 0;
/// y = 0;
/// t = 0;
/// while (x + 3 <= 20 && t <= tLimit) {
///     if (y <= 19) {
///         prob {
///             0.5 : y = y + 1; t = t + 1;
///             0.5 : y = y; t = t + 1;
///         }
///     }
///     else {
///         prob {
///             0.25 : x = x; t = t + 1;
///             0.25 : x = x + 1; t = t + 1;
///             0.25 : x = x + 2; t = t + 1;
///             0.25 : x = x + 3; t = t + 1;
///         }
///     }
/// }
/// { t <= tLimit }
/// Initialise the limit -- tLimit, then back to work on the two values again
/// qI0, m0, root -> qI0, m0, up count
/// 
/// 0 <= i <= tLimit:
///     qI{i}, m0, count -> qI{i + 1}, mCont, up count
/// 
/// qI{tLimit + 1}, m0, count -> qBack, mEnd , down
/// qBack, mCont, count -> qBack, mCont, down
/// qBack, m0, root -> qY0, mEnd, up count
///
/// 0 <= i <= 19:
///     qY{i}, mCont, count ->
///         0.5 -- qY{i}, mCont, up count
///         0.5 -- qY{i + 1}, mCont, up count
///     qY{i}, mEnd, count -> qBack, mEnd, down
/// 
/// qY20, mCont, count -> qX0
///
/// 0 <= i <= 17:
///     qX{i}, mCont, count ->
///         0.25 -- qX{i}, mCont, up count
///         0.25 -- qX{i + 1}, mCont, up count
///         0.25 -- qX{i + 2}, mCont, up count
///         0.25 -- qX{i + 3}, mCont, up count
///     qX{i}, mEnd, count -> qBack, mEnd, down
/// 
/// qX{18, 19, 20}, mCont, count -> Div  // may be ignored
/// qX{18, 19, 20}, mEnd, count -> qBack, mEnd, down
/// qBack, mEnd, root -> Ter
let genToolPrspeed tLimit =
    let qI i = Q $"qI{i}" in
    let m0 = M "m0" in
    let count = G "count" in
    let root = G "root" in
    let qBack = Q "qBack" in
    let mCont = M "mCont" in
    let qY i = Q $"qY{i}" in
    let mEnd = M "mEnd" in
    let qX i = Q $"qX{i}" in
    let rules =
        // qI0, m0, root -> qI0, m0, up count
        [(qI 0, m0, root) => (qI 0, m0, up count)] ++
        // 0 <= i <= tLimit:
        //     qI{i}, m0, count -> qI{i + 1}, mCont, up count
        flip List.map [0..tLimit] (fun i ->
            (qI i, m0, count) => (qI $ i + 1, mCont, up count)) ++
        // qI{tLimit + 1}, m0, count -> qBack, mEnd , down
        // qBack, mCont, count -> qBack, mCount, down
        // qBack, m0, root -> qY0, m0, up count
        [
            (qI $ tLimit + 1, m0, count) => (qBack, mEnd, down)
            (qBack, mCont, count) => (qBack, mCont, down)
            (qBack, m0, root) => (qY 0, mEnd, up count)
        ] ++
        // 0 <= i <= 19:
        //     qY{i}, mCont, count ->
        //         0.5 -- qY{i}, mCont, up count
        //         0.5 -- qY{i + 1}, mCont, up count
        //     qY{i}, mEnd, count -> qBack, mEnd, down
        List.concat (flip List.map [0..19] $ fun i ->
            [
                (qY i, mCont, count) => p 0.5 -- (qY i, mCont, up count)
                (qY i, mCont, count) => p 0.5 -- (qY $ i + 1, mCont, up count)
                (qY i, mEnd,  count) => (qBack, mEnd, down)
            ]) ++
        // qY20, mCont, count -> qX0
        [ (qY 20, mCont, count) => qX 0 ] ++
        // 0 <= i <= 17:
        //     qX{i}, mCont, count ->
        //         0.25 -- qX{i}, mCont, up count
        //         0.25 -- qX{i + 1}, mCont, up count
        //         0.25 -- qX{i + 2}, mCont, up count
        //         0.25 -- qX{i + 3}, mCont, up count
        //     qX{i}, mEnd, count -> qBack, mEnd, down
        List.concat (flip List.map [0..17] $ fun i ->
            [
                (qX i, mCont, count) => p 0.25 -- (qX i, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 1, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 2, mCont, up count)
                (qX i, mCont, count) => p 0.25 -- (qX $ i + 3, mCont, up count)
                (qX i, mEnd,  count) => (qBack, mEnd, down)
            ]) ++
        // qX{18, 19, 20}, mCount, count -> Div  // may be ignored
        // qX{18, 19, 20}, mEnd,   count -> qBack, mEnd, down
        flip List.map [18..20] (fun i ->
            (qX i, mEnd, count) => (qBack, mEnd, down)) ++
        // qEnd, mEnd, root -> Ter
        [
            (qBack, mEnd, root) => Ter
        ]
    in
    genModelFromFormattedRules (uint 2) (qI 0) m0 root rules
    
    
/// The PReMo comparison example for higher-dimensional expressions
/// The target expression is like:
/// x_0 = x_1
/// while for 0 < i < n:
///         1       1       n
/// x_i = ----- + ----- * \sum  x_j ... x_n
///       n + 1   n + 1   j = 1
///
/// So that all x_i for 1 <= i <= n are essentially the same with a large equation system
///
/// So we have an example that is quite complex to iterate.
///
/// There is a unique `q`
///
/// q, m0, root -> q, mEnd, up g1
///
/// 1 <= i <= n && 1 <= j <= n:
/// q, m0, g{i} -> {1/n-i+2} -- q, m{j}, up g{j}
/// (j /= n:) q, m{j}, g{i} -> q, m{j + 1}, up g{j + 1}
/// (j == n:) q, m{n}, g{i} -> q, mEnd, down
///
/// 1 <= i <= n:
/// q, m0, g{i} -> {1/n-i+2} -- q, mEnd, down
///
/// q, mEnd, root -> Ter
let genPReMoCmpHigherDimensional n =
    let q = Q "q" in
    let m i = M $"m{i}" in
    let g i = G $"g{i}" in
    let root = G "root" in
    let mEnd = M "mEnd" in
    let rules =
        [
            // q, m0, root -> q, mEnd, up g1
            [ (q, m 0, root) => (q, mEnd, up $ g 1) ]
            // 1 <= i <= n:
            flip List.map [1..n] (fun i ->
                [
                    // q, m0, g{i} -> {1/n-i+2} -- q, mEnd, down
                    [ (q, m 0, g i) => p $"1/{n+1}" -- (q, mEnd, down) ]
                    // 1 <= j <= n:
                    flip List.map [1..n] (fun j ->
                        [
                            // q, m0, g{i} ->
                            //     {1/n-i+2} -- q, m{j}, up g{j}
                            // (j /= n :) q, m{j}, g{i} -> q, m{j + 1}, up g{j + 1}
                            // (j == n :) q, m{j}, g{i} -> q, mEnd, down
                            (q, m 0, g i) => p $"1/{n+1}" -- (q, m j, up $ g j)
                            (q, m j, g i) =>
                                if j = n then (q, mEnd, down) else (q, m $ j + 1, up $ g (j + 1))
                        ]) |> List.concat
                ] |> List.concat) |> List.concat
            //
            // q, mEnd, root -> Ter
            [ (q, mEnd, root) => Ter ]
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint 1) q (m 0) root rules


/// x = 1/2 + 1/2 * x * x
///
/// That is:
/// S -> 0.5 -- \varepsilon | 0.5 -- S S
let genXEqHalfPlusHalfDouble _ =
    let q = Q "q" in
    let m0 = M "m0" in
    let mEnd = M "mEnd" in
    let mCont = M "mCont" in
    let root = G "root" in
    let g = G "g" in
    let proxyG = G "pg" in
    let rules =
        [
            [ (q, m0, root) => (q, mEnd, up g) ]
            flip List.map [ g; proxyG ] (fun rg ->
                [
                    (q, m0, rg) => p 0.5 -- (q, mCont, up g)
                    (q, m0, rg) => p 0.5 -- (q, mEnd,  down)
                    (q, mCont, rg) => (q, mEnd, up proxyG)
                    (q, mEnd,  rg) => (q, mEnd, down)
                ] ) |> List.concat
            [ (q, mEnd, root) => Ter ]
        ] |> List.concat
    in
    genModelFromFormattedRules (uint 1) q m0 root rules
    
    
/// { X = xStart }
/// while (X >= 0 && X <= 1000) {
///     prob {
///         0.5 : X = X - 2;
///         0.5 : X = X + 1;
///     }
/// }
/// { X <= 1000 }
///
/// Implementation: Just a Markov chain.
let gen1DWalk (xStart : int) =
    let x i = Q $"x{i}" in
    let m0 = M "m0" in
    let root = G "root" in
    let rules =
        flip List.map [0..1000] (fun i ->
            [
                if i > 2 then
                    (x i, m0, root) => p 0.5 -- (x $ i - 2)
                if i = 1000 then
                    (x i, m0, root) => p 0.5 -- Ter
                else
                    (x i, m0, root) => p 0.5 -- (x $ i + 1)
            ])
        |> List.concat
    in
    genModelFromFormattedRules (uint 1) (x xStart) m0 root rules
    
    
/// The TreeShape example with possibility of divergence at EACH NODE
/// The above one only works for a special kind of node
let genTreeShapeTotalRandomTraversal shortcutType times =
    let q = Q "q" in
    let m i = M $"m{i}" in
    let gL = G "gL" in
    let gR = G "gR" in
    let visitedLeft = M "visitedLeft" in
    let visitedRight = M "visitedRight" in
    let leaf = M "leaf" in
    let toRevisit = M "toRevisit" in
    let root = G "root" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let rules =
        [
            // root rules
            flip List.map [0..times-1] (fun idx ->
                (q, m idx, root) => (q, m $ idx + 1, up gL))
            [
                (q, m times, root) => Ter
            ]
            // the symmetric relay rules of `gL` and `gR`
            flip List.map [ gL; gR ] (fun g -> [
                // initial usual node
                (q, m 0, g) => p "1/2" -- (q, visitedLeft, up gL)
                (q, m 0, g) => p "1/2" -- (q, leaf, down)
                // middle relay rules
                (q, toRevisit, g) => p "2/3" -- (q, visitedLeft, up gL)
                (q, toRevisit, g) => p "1/3" -- shortcutOp
                (q, visitedLeft, g) => (q, visitedRight, up gR)
                (q, visitedRight, g) => (q, toRevisit, down)
                (q, leaf, g) => p "2/3" -- (q, leaf, down)
                (q, leaf, g) => p "1/3" -- shortcutOp
            ]) |> List.concat
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint times) q (m 0) root rules
    
    
let genQueueWithDifferentABBehavior (pA : string) (pB : string) (pEnd : string) shortcutType times =
    let q = Q "q" in
    // q0
    let qBack = Q "qBack" in
    let m i = M $"m{i}" in
    let mA i = M $"mA{i}" in
    let mB = M "mB" in
    let mEnd = M "mEnd" in
    let root = G "root" in
    let g = G "g" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let rules =
        [
            flip List.map [0..times-1] (fun idx ->
                (qBack, m idx, root) => (q, m $ idx + 1, up g))
            [
                (qBack, m times, root) => Ter
            ]
            [
                // define initial up
                (q, m 0, g)      => pA   -- (q, mA 1, up g)
                (q, m 0, g)      => pB   -- (q, mB, up g)
                (q, m 0, g)      => pEnd -- (qBack, mEnd, down)
                (qBack, mA 1, g) => (qBack, mA 1, down)
                (qBack, mB,   g) => (qBack, mB, down)
                // define new up
                (q, mEnd, g)     => (qBack, mEnd, down)
                (q,  mB,  g)     => (    q,   mB, up g)
            ]
            // revisit `A`
            List.concat (flip List.map [1..times-1] $ fun idx -> [
                (q, mA idx, g) => $"{idx}/{idx + 1}" -- (q, mA $ idx + 1, up g)
                (q, mA idx, g) => $"1/{idx + 1}"     -- shortcutOp
                (qBack, mA $ idx + 1, g) => (qBack, mA $ idx + 1, down)
            ])
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint times) qBack (m 0) root rules
    
    
let genTreeShapeWithVariantOrientations toShortcutDiverge nonLeafProb times =
    let qL = Q "qL" in
    let qR = Q "qR" in
    // this is to make the guessing result unique, also q0
    let qBack = Q "qBack" in
    let m i = M $"m{i}" in
    let gL = G "gL" in
    let gR = G "gR" in
    let toVisitLeft = M "toVisitLeft" in
    let toVisitRight = M "toVisitRight" in
    let toVisited = M "toVisited" in
    let visited = M "visited" in
    let leaf = M "leaf" in
    let root = G "root" in
    let rules =
        [
            // the bottom is just a relay place
            // the initial traversal strategy is `L`eft-oriented
            [
                (qBack, m 0, root) => (qL, m 1, up gL)
            ]
            // otherwise, the traversal can be either `L`eft- or `R`ight-oriented
            List.concat (flip List.map [1..times-1] $ fun idx -> [
                (qBack, m idx, root) => "1/2" -- (qL, m $ idx + 1, up gL)
                (qBack, m idx, root) => "1/2" -- (qR, m $ idx + 1, up gL)
            ])
            [
                (qBack, m times, root) => Ter
            ]
            // left and right visiting rules
            List.concat (flip List.map [ gL; gR ] $ fun g -> [
                (qL, m 0, g) => nonLeafProb          -- (qL, toVisitRight, up gL)
                (qL, m 0, g) => $"1 - {nonLeafProb}" -- (qBack, leaf, down)
                
                (qBack, toVisitRight, g) => (qL, toVisited, up gR)
                
                (qBack, toVisited, g) => (qBack, visited, down)
                
                if toShortcutDiverge then
                    (qL, visited, g) => "2/3" -- (qL, toVisitRight, up gL)
                    (qL, visited, g) => "1/3" -- OpDiv
                    
                    (qR, visited, g) => "2/3" -- (qR, toVisitLeft, up gR)
                    (qR, visited, g) => "1/3" -- OpDiv
                else
                    (qL, visited, g) => (qL, toVisitRight, up gL)
                    
                    (qR, visited, g) => (qR, toVisitLeft, up gR)
                
                (qBack, toVisitLeft, g) => (qR, toVisited, up gL)
                
                (qL, leaf, g) => (qBack, leaf, down)
                (qR, leaf, g) => (qBack, leaf, down)
            ])
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint times) qBack (m 0) root rules
    
    
/// just a synonym of `genTreeShapeWithVariantOrientations`
let genTreeShapeGRT toShortcutDiverge nonLeafProb times =
    genTreeShapeWithVariantOrientations toShortcutDiverge nonLeafProb times
    
    
/// locally determine the data
let genTreeShapeLRT toShortcutDiverge nonLeafProb times =
    let q = Q "q" in
    let m i = M $"m{i}" in
    let gL = G "gL" in
    let gR = G "gR" in
    let toVisitLeft = M "toVisitLeft" in
    let toVisitRight = M "toVisitRight" in
    let toVisited = M "toVisited" in
    let visited = M "visited" in
    let leaf = M "leaf" in
    let root = G "root" in
    let rules =
        [
            flip List.map [0..times-1] (fun idx ->
                (q, m idx, root) => (q, m $ idx + 1, up gL))
            [
                (q, m times, root) => Ter
            ]
            List.concat (flip List.map [ gL; gR ] $ fun g -> [
                (q, m 0, g) => nonLeafProb          -- (q, toVisitRight, up gL)
                (q, m 0, g) => $"1 - {nonLeafProb}" -- (q, leaf, down)
                
                (q, toVisitRight, g) => (q, toVisited, up gR)
                (q, toVisitLeft, g) => (q, toVisited, up gL)
                
                (q, toVisited, g) => (q, visited, down)
                
                if toShortcutDiverge then
                    (q, visited, g) => "1/3" -- (q, toVisitRight, up gL)
                    (q, visited, g) => "1/3" -- (q, toVisitLeft, up gR)
                    (q, visited, g) => "1/3" -- OpDiv
                else
                    (q, visited, g) => "1/2" -- (q, toVisitRight, up gL)
                    (q, visited, g) => "1/2" -- (q, toVisitLeft, up gR)
                
                (q, leaf, g) => (q, leaf, down)
            ])
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint times) q (m 0) root rules
    
    
let genQueueGlobalRandomServe pA pB pEnd pSA shortcutType times =
    let qInit = Q "qInit" in
    let qA = Q "qA" in
    let qB = Q "qB" in
    // q0
    let qBack = Q "qBack" in
    let m i = M $"m{i}" in
    let mA i = M $"mA{i}" in
    let mB i = M $"mB{i}" in
    let mEnd = M "mEnd" in
    let root = G "root" in
    let g = G "g" in
    let shortcutOp =
        match shortcutType with
        | ShortcutTermination -> OpTer
        | ShortcutDivergence  -> OpDiv
    in
    let rules =
        [
            List.concat (flip List.map [1..times-1] $ fun idx -> [
                (qBack, m idx, root) => pSA -- (qA, m $ idx + 1, up g)
                (qBack, m idx, root) => $"1 - {pSA}" -- (qB, m $ idx + 1, up g)
            ])
            [
                (qInit, m 0, root) => (qInit, m 1, up g)
                (qBack, m times, root) => Ter
            ]
            [
                // define initial up
                (qInit, m 0, g)      => pA   -- (qInit, mA 1, up g)
                (qInit, m 0, g)      => pB   -- (qInit, mB 1, up g)
                (qInit, m 0, g)      => pEnd -- (qBack, mEnd, down)
                (qBack, mA 1, g) => (qBack, mA 1, down)
                (qBack, mB 1, g) => (qBack, mB 1, down)
                // define new up
                (qA, mEnd, g) => (qBack, mEnd, down)
                (qB, mEnd, g) => (qBack, mEnd, down)
            ]
            // revisit `A` and `B`
            List.concat (flip List.map [1..times-1] $ fun idx ->
            List.concat (flip List.map [(qA, qB, mA); (qB, qA, mB)] $ fun (q, oq, m) -> [
                (q,  m idx, g) => $"{idx}/{idx + 1}" -- (q, m $ idx + 1, up g)
                (q,  m idx, g) => $"1/{idx + 1}"     -- shortcutOp
                (oq, m idx, g) => (oq, m $ idx + 1, up g)
                (qBack, m $ idx + 1, g) => (qBack, m $ idx + 1, down)
            ]))
        ]
        |> List.concat
    in
    genModelFromFormattedRules (uint times) qInit (m 0) root rules
    