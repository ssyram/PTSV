module PTSV.ShortAlgorithms

open System.Collections.Generic
open PTSV.Utils

type Graph<'v> =
    {
        /// V
        nodes : 'v list;
        /// E
        nextNodes : 'v -> 'v list; 
    }
type HashGraph<'v> =
    {
        nodes : 'v list;
        nextNodes : HashMap<'v, 'v list>; 
    }
    with
    member x.toGraph : Graph<'v> =
        {
            nodes = x.nodes;
            nextNodes = fun v -> Option.defaultValue [] $ x.nextNodes.tryFind v
        }
    end

module Graph = begin
    let dfsOrder (graph : Graph<'v>) =
        let visitedSet = HashSet () in 
        let rec foldFunc (stk : 'v list) (v : 'v) = 
            if visitedSet.Add v then v :: List.fold foldFunc stk (graph.nextNodes v)
            else stk in 
        List.fold foldFunc [] graph.nodes
    let hashMapToGraph (map : HashMap<_,_>) =
        {
            nodes = Seq.toList $ Seq.map fst map;
            nextNodes = map
        }.toGraph
    let reverse (graph : Graph<'v>) : HashGraph<'v> =
        let newData = HashMap () in 
        foldWith graph.nodes () $ fun v () -> foldWith (graph.nextNodes v) () $ fun vk () ->
            flip (HashMap.compute vk) newData $ fun maybeSet ->
                let set = Option.defaultValue (HashSet ()) maybeSet in
                set.Add v |> ignore;
                Some set
        {
            nodes = graph.nodes; 
            nextNodes = HashMap.map toList newData; 
        }
end

let stronglyConnectedComponents (graph : Graph<'v>) : HashSet<'v> list =
    let stk = Graph.dfsOrder graph in
    let revGraph = (Graph.reverse graph).toGraph in
    let visited = HashSet () in
    let rec core stk ret = 
        match stk with
        | [] -> ret
        | h :: lst -> if visited.Contains h
                         then core lst ret
                         else let scc = searchData h $ HashSet () in 
                              visited.UnionWith scc; 
                              core lst $ scc :: ret 
    and searchData h tmpVisited =
        if not (visited.Contains h) && tmpVisited.Add h then 
            foldWith (revGraph.nextNodes h) tmpVisited searchData
        else tmpVisited in  
    core stk [] 

let bottomStronglyConnectedComponents (graph : Graph<'v>) : HashSet<'v> list =
    let notGoingOut (set : HashSet<_>) = flip Seq.forall set $ fun v ->
        Seq.forall set.Contains $ graph.nextNodes v in
    List.filter notGoingOut $ stronglyConnectedComponents graph

let stronglyConnectedComponentsGraph (graph : Graph<'v>) : HashGraph<Set<'v>> = 
    let stk = Graph.dfsOrder graph in  // stk should contain all nodes
    let revGraph = (Graph.reverse graph).toGraph in 
    let visited = HashSet () in
    let sccData = HashMap<'v, Set<'v>> () in 
    let rec core = function
                   | []       -> ()
                   | h :: lst -> if visited.Contains h
                                   then core lst
                                   else let scc = searchData h Set.empty in
                                        visited.UnionWith scc;
                                        flip HashMap.union sccData $ zip scc (repeat scc)
    and searchData h tmpVisited = 
        if not (visited.Contains h) && not (Set.contains h tmpVisited) then
            foldWith (revGraph.nextNodes h) (Set.add h tmpVisited) searchData
        else tmpVisited in
    core stk;
    let retNodes = HashSet<Set<'v>> () in 
    let retData = HashMap () in 
    forEach graph.nodes begin fun v -> 
        let vSet = sccData[v] in 
        retNodes.Add vSet |> ignore; 
        forEach (graph.nextNodes v) $ fun v' -> 
            flip (HashMap.compute vSet) retData $ fun maybeSet -> 
                let set = Option.defaultValue (HashSet ()) maybeSet in
                set.Add sccData[v'] |> ignore;
                Some set end; 
    {
        nodes = toList retNodes;
        nextNodes = HashMap.map toList retData; 
    }

/// to systematically enumerate the information
module Enumerate = begin
    let private getExactN k =
        // the guessN should be the case, but the sqrt computation may lead to some bias
        let guessN =
            // (n + 1) * n / 2 <= k < (n + 2) * (n + 1) / 2
            // get sqrt(2 * k + 1/4) - 3/2 < n <= sqrt(2 * k + 1/4) - 1/2
            // so just get the floor int of (sqrt(2 * k + 1/4) - 1/2)
            int $ sqrt (2.0 * float k + 0.25) - 1.0 / 2.0 in
        let rec smaller n =
            if (n + 1) * n / 2 > k then smaller (n - 1) else n in
        let rec bigger n =
            if (n + 2) * (n + 1) / 2 <= k then bigger (n + 1) else n in
        smaller $ bigger guessN
    /// enumerate the 2D index
    let getTwoD k =
        // there may be some kind of accuracy difference like n + 1 or n - 1
        let n = getExactN k in
        let dif = k - (n + 1) * n / 2 in
        (n - dif, dif)
    let rec getMultipleDimensions dim k =
        if dim <= 0 then []
        elif dim = 1 then [ k ]
        else let this, that = getTwoD k in
             this :: getMultipleDimensions (dim - 1) that
end
