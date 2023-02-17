module PTSV.PAHORSExampleGenerator

open Global
open Utils

let genPAHORSTreeGen times =
    let rec nTimesF times =
        if times = 1 then "F x"
        elif times = 0 then "x"
        else $"F ({nTimesF $ times - 1})"
    in
    $"""
%%BEGIN PAHORS type
S : o
F : o -> o
%%END PAHORS type

%%BEGIN PAHORS grammar
S := F \top.
F x (0.5):= x.
F x (0.5):= {nTimesF times}.
%%END PAHORS grammar
    """


let genPAHORSTreeGenWithDiversity times =
    let rec nTimesF times =
        if times = 1 then "F x"
        elif times = 0 then "x"
        else $"F ({nTimesF $ times - 1})"
    in
    let genFx times =
        $"F x (1/(n+1)):= {nTimesF times}."
    in
    let defFx =
        List.map genFx [0..times]
        |> String.concat "\n"
    in
    $"""
let n = {times}
%%BEGIN PAHORS type
S : o
F : o -> o
%%END PAHORS type

%%BEGIN PAHORS grammar
S := F \top.
{defFx}
%%END PAHORS grammar
    """
