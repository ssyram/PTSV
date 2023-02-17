module PTSV.Externals

// some external functions that are irrelevant yet supportive to the projects

open Utils
open PTSV
open ExampleGenerators
open PAHORSExampleGenerator
open System.IO
    
let saveExamplesToFiles (directory : string) examplesWithNames =
    let directory =
        match directory.ToLower () with
        | "rptsa" -> "k-PTSA"
        | "pahors" -> "PAHORS"
        | "ppda" -> "PPDA"
        | otherDirectory -> otherDirectory
    in
    let fileToSave (name : string) =
        $"../../../examples/{directory}/example {name}.txt"
    in
    let saveOneExample (name, example) =
        File.WriteAllText(fileToSave name, example)
    in
    Seq.iter saveOneExample examplesWithNames
    
    
/// the two styles of examples should be able to convert to each other
let private convertExampleWithNamesToGeneratorsAndParas examplesWithNames =
    let names = Seq.map fst examplesWithNames in
    let map = Map.ofSeq examplesWithNames in
    (flip Map.find map, names)
    
let private convertGeneratorsAndParasToExamplesWithNames name generator paras =
    let printName name para =
        match name with
        | "" -> $"{para}"
        | _  -> $"{name} ({para})"
    in
    List.map (fun para -> (printName name para, generator para)) paras
    
    
let saveGeneratedPAHORSExamples () =
    let examples =
        [
            "ngen", genPAHORSTreeGen, [1; 3; 6; 9]
            "vgen", genPAHORSTreeGenWithDiversity, [1..4]
        ]
        |> List.map (fun (n,g,p) -> convertGeneratorsAndParasToExamplesWithNames n g p)
        |> List.concat
    in
    saveExamplesToFiles "PAHORS" examples


let saveGeneratedPaperExamples () =
    [
        "Random Paths", genKDyckLanguagesWithRandomUp "1/2", [1..13]
        "Repeated LR Traversal (1d2)", genTreeShapeGRT false "1/2", [1..13]
        "Repeated LR Traversal (1d3)", genTreeShapeGRT false "1/3", [1..13]
        "Repeated LR Traversal (2d3)", genTreeShapeGRT false "2/3", [1..14]
        "Repeated L Traversal (1d3)", genKDyckLanguages "1/3", [
            10; 20; 50; 100; 200; 500; 1000
        ]
        "Queueing", genQueueGlobalRandomServe "1/2" "1/3" "1/6" "1/4" ShortcutTermination, [1..11]
        "Queueing(A)", genQueueWithDifferentABBehavior "1/2" "1/3" "1/6" ShortcutTermination, [
            10; 20; 50; 100; 200
        ]
        "PAHORS NTreegen", genPAHORSTreeGen, [1..9]
        "PAHORS VTreegen", genPAHORSTreeGenWithDiversity, [1..4]
    ]
    |> List.map (fun (n,g,p) -> convertGeneratorsAndParasToExamplesWithNames n g p)
    |> List.concat
    |> saveExamplesToFiles "paper examples"

let renameAndMovePAHORSExamples () =
    let mapping =
        [
            "Ex2.3", "example phors 2.3"
            "Listgen", "example phors listgen"
            "Treegen", "example 5"
            "ListEven", "example 10 (listeven)"
            "ListEven2", "example 11"
            "Ex5.4(0, 0)", "example 9 (0 0)"
            "Ex5.4(0.3, 0.3)", "example 9 (3 3)"
            "Ex5.4(0.5, 0.5)", "example 9 (5 5)"
            "TreeEven(0.5)", "example 12"
            "TreeEven(0.49)", "example 12 (49)"
            "TreeEven(0.51)", "example 12 (51)"
            "Discont(0.01, 0.99)", "example 8"
            "Example 4.9", "example 7"
            "Printer", "example 3.1 (Heavy)"
        ]
    in
    let fetchExampleContent name =
        File.ReadAllText($"../../../examples/PAHORS/{name}.txt")
    in
    let writeExample newName content =
        File.WriteAllText($"../../../examples/paper examples/example {newName}.txt", content)
    in
    let iterFunc (newName, oldName) =
        writeExample newName $ fetchExampleContent oldName
    in
    List.iter iterFunc mapping
