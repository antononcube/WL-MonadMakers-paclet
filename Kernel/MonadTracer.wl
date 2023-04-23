(* Mathematica Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: MonadTracer *)
(* :Context: MonadTracer` *)
(* :Author: Anton Antonov *)
(* :Date: 2023-04-23 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 13.1 *)
(* :Copyright: (c) 2023 Anton Antonov *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["AntonAntonov`MonadMakers`MonadTracer`"];

(*$TraceMonadFailure::usage = "Failure symbol for TraceMonad.";*)

(*TraceMonadUnit::usage = "Lifting a monad object into TraceMonad.";*)

(*TraceMonadBind::usage = "The binding function of TraceMonad.";*)

(*TraceMonadEchoGrid::usage = "Echoes a tabulation of the traced monad functions using Grid.";*)

(*TraceMonadTakeGrid::usage = "Gives a tabulation of the traced monad functions using Grid.";*)

(*Grid87::usage = "A modified version of Grid.";*)

Begin["`Private`"];


ClearAll[$TraceMonadFailure];
(*$TraceMonadFailure = None;*)

(**************************************************************)
(* Generation                                                 *)
(**************************************************************)
Needs["AntonAntonov`MonadMakers`"];
Needs["AntonAntonov`MonadMakers`StateMonadCodeGenerator`"];

GenerateStateMonadCode["AntonAntonov`MonadMakers`TraceMonad", "StringContextNames" -> False, "FailureSymbol" -> $TraceMonadFailure ];

(**************************************************************)
(* Infix operators                                            *)
(**************************************************************)

(* Not needed here -- should have been already done by GenerateStateMonadCode. *)
(*DoubleLongRightArrow[x_?TraceMonadUnitQ, f_] := TraceMonadBind[x, f];*)


(**************************************************************)
(* Monad specific functions                                   *)
(**************************************************************)


ClearAll[TraceMonadUnit];

SetAttributes[TraceMonadUnit, HoldAll];

TraceMonadUnit[x_] := TraceMonadUnit[x, DoubleLongRightArrow ];

TraceMonadUnit[x_, binder_Symbol] :=
    TraceMonad[x, <|"data" -> HoldForm[x], "binder" -> binder, "commands" -> {}, "comments" -> {""}, "contextKeys" -> {{}} |>];

ClearAll[TraceMonadBind];

TraceMonadBind[___] := $TraceMonadFailure;

TraceMonadBind[TraceMonad[x_, context_], f_] :=
    Block[{res = f[x, context]}, If[FreeQ[res, $TraceMonadFailure], res, $TraceMonadFailure]] /;
        TrueQ[StringMatchQ[ToString[f], "TraceMonad" ~~ __]];

TraceMonadBind[TraceMonad[x_, context_], com_String] :=
    Block[{res},
      TraceMonad[x, Join[context, <|"comments" -> ReplacePart[context["comments"], -1 -> com]|>]]
    ];

TraceMonadBind[TraceMonad[x_, context_], f_] :=
    Block[{res},
      res = context["binder"][x, f];
      Which[

        (* Applying a heuristic for the failure symbol of the wrapped monad. *)
        res === None || Developer`SymbolQ[res] && StringMatchQ[SymbolName[res], "$"~~___~~"Failure"~~___],
        TraceMonadEchoGrid[][x, context];
        res, (* This should not be $TraceMonadFailure .*)

        Length[res] >= 2 && AssociationQ[ res[[2]] ],
        (* Assuming State monad. *)
        TraceMonad[res,
          Join[context,
            <|"commands" -> Append[context["commands"], f],
              "comments" -> Append[context["comments"], ""],
              "contextKeys" -> Append[context["contextKeys"], Keys[res[[2]]] ] |>]
        ],

        True,
        TraceMonad[res,
          Join[context,
            <|"commands" -> Append[context["commands"], f],
              "comments" -> Append[context["comments"], ""],
              "contextKeys" -> Append[context["contextKeys"], {}]|>]
        ]

      ]
    ];


ClearAll[Grid87];

Grid87 = Framed@
    Grid[#, Alignment -> Left, Dividers -> All, FrameStyle -> Directive[Dashing[2], GrayLevel[0.87]]] &;


ClearAll[TraceMonadEchoGrid];

Options[TraceMonadEchoGrid] = { "ComplexStyling" -> True, "ContextKeys" -> False };

TraceMonadEchoGrid[x_, context_Association] := TraceMonadEchoGrid[][x, context];

TraceMonadEchoGrid[][x_, context_] := TraceMonadEchoGrid[Grid87][x, context];

TraceMonadEchoGrid[opts:OptionsPattern[] ][x_, context_] := TraceMonadEchoGrid[Grid87, opts ][x, context];

TraceMonadEchoGrid[gridFunc_, opts:OptionsPattern[] ][x_, context_] :=
    Block[{res},

      res = TraceMonadBind[ TraceMonad[x, context], TraceMonadTakeGrid[gridFunc, opts] ];

      (* Show result *)
      Echo[res];
      TraceMonad[x, context]
    ];


ClearAll[TraceMonadTakeGrid];

Options[TraceMonadTakeGrid] = Options[TraceMonadEchoGrid];

TraceMonadTakeGrid[x_, context_Association] := TraceMonadTakeGrid[][x, context];

TraceMonadTakeGrid[][x_, context_] := TraceMonadTakeGrid[Grid87][x, context];

TraceMonadTakeGrid[opts:OptionsPattern[] ][x_, context_] := TraceMonadTakeGrid[Grid87, opts ][x, context];

TraceMonadTakeGrid[gridFunc_, opts:OptionsPattern[] ][x_, context_] :=
    Block[{grData, delim, cStyleQ, cKeysQ},

      cStyleQ = TrueQ[OptionValue[TraceMonadTakeGrid, "ComplexStyling"]];
      cKeysQ = TrueQ[OptionValue[TraceMonadTakeGrid, "ContextKeys"]];

      If[ !cKeysQ,
        grData =
            Transpose[{Prepend[HoldForm /@ context["commands"], context["data"]], context["comments"]}],
        (* ELSE *)
        grData =
            Transpose[{Prepend[HoldForm /@ context["commands"], context["data"]], context["comments"], context["contextKeys"]}];
      ];

      If[ context["binder"] === NonCommutativeMultiply, delim = "**", delim = "\[DoubleLongRightArrow]"];
      delim = "\[ThinSpace]" <> delim;

      (* Style the code and comments *)
      If[ cStyleQ,
        (* Using RuleCondition because the pipeline functions are kept in HoldForm. *)
        (* Note that RuleCondition is undocumented. *)
        (* The alternative is to use /. (z_String :> With[{eval = "\"" <> z <> "\""}, eval /; True]) *)
        grData[[All, 1]] =
            Map[
              Row[{"  ",
                Style[ # /. (z_String :> RuleCondition[("\"" <> z <> "\"")]), "Input"],
                Style[delim, "Input"]}] &,
              grData[[All, 1]]],
        (* ELSE *)
        grData[[All, 1]] = Map[Row[{"  ", Style[#, "Input"], Style[delim, "Input"]}] &, grData[[All, 1]]];
      ];
      grData[[1, 1]] = Row[Rest@grData[[1, 1, 1]]];
      grData[[-1, 1]] = Row[Most@grData[[-1, 1, 1]]];
      grData[[All, 2]] =
          Map[Style[#, "CommentStyle" /. Options[$FrontEnd, AutoStyleOptions][[1, 2]]] &, grData[[All, 2]]];

      If[Dimensions[grData][[2]] == 3, (*i.e. cKeysQ *)
        grData[[All, 3]] =
            Map[Style[#, "CommentStyle" /. Options[$FrontEnd, AutoStyleOptions][[1, 2]]] &, grData[[All, 3]]];
      ];

      (* Show result *)
      gridFunc[grData]
    ];


End[]; (* `Private` *)

EndPackage[]