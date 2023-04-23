(* Mathematica Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: StateMonadGenerator *)
(* :Context: StateMonadGenerator` *)
(* :Author: Anton Antonov *)
(* :Date: 2023-04-23 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 13.1 *)
(* :Copyright: (c) 2023 Anton Antonov *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["AntonAntonov`MonadMakers`StateMonadGenerator`"];

(*GenerateStateMonadCode::usage = "GenerateStateMonadCode[monadName_String] generates the basic functions \*)
(*of a State monad that allows computations with a mutable context. Code for handling context string names \*)
(*is generated depending on the Boolean values of the option \"StringContextNames\". \*)
(*Monad's failure symbol is specified with the option \"FailureSymbol\".";*)

(*AssociationModule::usage = "AssociationModule[asc_Association, body_] transforms the elements of asc into \*)
(*symbol assignments ascAssign and executes Module[ ascAssign, body ]. The keys of asc are assumed to be strings.";*)

(*GenerateMonadDroper::usage = "GenerateMonadDroper[monadName_String, elementName_String] generates monadic \*)
(*droper functions for specified monad and element names.";*)

(*GenerateMonadSetter::usage = "GenerateMonadSetter[monadName_String, elementName_String] generates monadic \*)
(*setter functions for specified monad and element names.";*)

(*GenerateMonadTaker::usage = "GenerateMonadTaker[monadName_String, elementName_String] generates monadic \*)
(*taker functions for specified monad and element names.";*)

(*GenerateMonadAccessors::usage = "GenerateMonadAccessors[monadName_String, elementNames:{_String..}] generates monadic \*)
(*droper, setter, and taker functions for specified monad and element names.";*)

Begin["`Private`"];

Needs["AntonAntonov`MonadMakers`"];

Attributes[AssociationModule] = HoldRest;
AssociationModule[asc_Association, body_] :=
    Replace[Join @@
        Cases[Hold @@ Normal @@ {asc},
          h_[L : _Symbol | _String, R_] :>
              With[{sy = Quiet@Symbol@ToString@L},
                Hold[h[sy, R]] /; Depth[sy] === 1]], {(a_ -> b_) :> (a = b), (a_ :> b_) :> (a := b)}, {1}] /.
        _[sets__] :> Module[{sets}, body];

ClearAll[GenerateStateMonadCode];
Options[GenerateStateMonadCode] = {"StringContextNames" -> True, "FailureSymbol" -> None, "EchoFailingFunction" -> True};
GenerateStateMonadCode[monadName_String, opts : OptionsPattern[]] :=
    With[{
      MState = ToExpression[monadName],
      MStateBind = ToExpression[monadName <> "Bind"],
      MStateAddToContext = ToExpression[monadName <> "AddToContext"],
      MStateAssignTo = ToExpression[monadName <> "AssignTo"],
      MStateAssignContextTo = ToExpression[monadName <> "AssignContextTo"],
      MStateAssignValueTo = ToExpression[monadName <> "AssignValueTo"],
      MStateContexts = ToExpression[monadName <> "Contexts"],
      MStateDropFromContext = ToExpression[monadName <> "DropFromContext"],
      MStateEcho = ToExpression[monadName <> "Echo"],
      MStateEchoContext = ToExpression[monadName <> "EchoContext"],
      MStateEchoFailingFunction = TrueQ[OptionValue["EchoFailingFunction"]],
      MStateEchoFunctionContext = ToExpression[monadName <> "EchoFunctionContext"],
      MStateEchoFunctionValue = ToExpression[monadName <> "EchoFunctionValue"],
      MStateEchoValue = ToExpression[monadName <> "EchoValue"],
      MStateFail = ToExpression[monadName <> "Fail"],
      MStateFailureSymbol = OptionValue["FailureSymbol"],
      MStateFold = ToExpression[monadName <> "Fold"],
      MStateIf = ToExpression[monadName <> "If"],
      MStateIfElse = ToExpression[monadName <> "IfElse"],
      MStateIterate = ToExpression[monadName <> "Iterate"],
      MStateModifyContext = ToExpression[monadName <> "ModifyContext"],
      MStateModule = ToExpression[monadName <> "Module"],
      MStateNest = ToExpression[monadName <> "Nest"],
      MStateNestWhile = ToExpression[monadName <> "NestWhile"],
      MStateOption = ToExpression[monadName <> "Option"],
      MStatePutContext = ToExpression[monadName <> "PutContext"],
      MStatePutValue = ToExpression[monadName <> "PutValue"],
      MStateRetrieveFromContext = ToExpression[monadName <> "RetrieveFromContext"],
      MStateSetContext = ToExpression[monadName <> "SetContext"],
      MStateSetValue = ToExpression[monadName <> "SetValue"],
      MStateSucceed = ToExpression[monadName <> "Succeed"],
      MStateTakeContext = ToExpression[monadName <> "TakeContext"],
      MStateTakeValue = ToExpression[monadName <> "TakeValue"],
      MStateUnit = ToExpression[monadName <> "Unit"],
      MStateUnitQ = ToExpression[monadName <> "UnitQ"],
      MStateWhen = ToExpression[monadName <> "When"]
    },

      ClearAll[MState, MStateUnit, MStateUnitQ, MStateBind, MStateFail, MStateSucceed, MStateEcho,
        MStateEchoValue, MStateEchoFunctionValue,
        MStateEchoContext, MStateEchoFunctionContext,
        MStatePutContext, MStatePutValue, MStateModifyContext,
        MStateAddToContext, MStateRetrieveFromContext,
        MStateOption, MStateWhen, MStateIfElse, MStateIterate,
        MStateIf, MStateNest, MStateNestWhile, MStateFold,
        MStateModule, MStateContexts,
        MStateSetContext, MStateSetValue
      ];

      (* What are the assumptions for monad's failure symbol? *)
      (*If[ !MemberQ[Attributes[MStateFailureSymbol], System`Protected]], ClearAll[MStateFailureSymbol] ];*)

      MStateBind::ffail = "Failure when applying: `1`";
      MStateBind::mscxt = "The result is missing a context. Reusing the context argument.";
      MStateContexts::nocxt = "The string \"`1`\" does not refer to a known context.";
      MStateContexts::nocxtp = MStateContexts::nocxt <> " Associating with an empty context and proceeding.";

      MStateFail[x_, context_Association] := MStateFailureSymbol;
      MStateFail[][x_, context_] := MStateFailureSymbol;
      MStateFail[s__][x_, context_] := Fold[ MStateBind, MStateUnit[x, context], { MStateEcho[s], MStateFail[] }];
      (*MStateFail[echoArgs__][x_, c:(_String|_Association)] := (Echo[echoArgs]; MStateFailureSymbol);*)
      MStateFail::usage = "Failure.";

      MStateSucceed[x_, context_] := MStateUnit[{}, context];
      MStateSucceed[][x_, context_] := MStateUnit[{}, context];
      MStateSucceed[s__][x_, context_] := MStateUnit[s, context];
      MStateSucceed::usage = "Success.";

      MStateUnit[MStateFailureSymbol] := MStateFailureSymbol;
      MStateUnit[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateUnit[] := MState[None, <||>];
      MStateUnit[x_] := MState[x, <||>];
      MStateUnit[{x_, c : (_String | _Association)}] := MState[x, c];
      MStateUnit[ x_, c : (_String | _Association) ] := MState[x, c];
      MStateUnit::usage = SymbolName[MState] <> " monad unit constructor.";

      MStateUnitQ[x_] := MatchQ[x, MStateFailureSymbol] || MatchQ[x, MState[_, _Association]];
      MStateUnitQ::usage = SymbolName[MState] <> " monad unit test.";

      MStateBind[MStateFailureSymbol] := MStateFailureSymbol;
      MStateBind[MState[x_, context_Association], f_] :=
          Block[{res = f[x, context]},
            Which[
              !FreeQ[res, MStateFailureSymbol],

              If[MStateEchoFailingFunction,
                With[{ef = ToString @ If[ LeafCount[HoldForm[f]] > 200, StringTake[ToString[f], UpTo[300]] <> "...", HoldForm[f] ] },
                  Echo[
                    TemplateApply[StringTemplate[MStateBind::ffail], ef], ToString[MStateBind] <> ":" ]
                ]
              ];
              MStateFailureSymbol,

              MatchQ[res, MState[_]],

              If[MStateEchoFailingFunction,
                With[{ef = ToString @ If[ LeafCount[HoldForm[f]] > 200, StringTake[ToString[f], UpTo[300]] <> "...", HoldForm[f] ] },
                  Echo[
                    TemplateApply[StringTemplate[MStateBind::mscxt], ef], ToString[MStateBind] <> ":"]
                ]
              ];
              MState[res[[1]], context],

              True, res
            ]
          ];
      If[TrueQ[OptionValue["StringContextNames"]],
        MStateBind[MState[x_, context_String], f_] :=
            Block[{res},
              If[! MatchQ[MStateContexts[context], _Association],
                Echo[TemplateApply[StringTemplate[MStateContexts::nocxtp], context]];
                MStateContexts[context] = <||>;
              ];
              res = f[x, MStateContexts[context]];
              Which[
                ! FreeQ[res, MStateFailureSymbol],
                If[MStateEchoFailingFunction,
                  With[{ef = ToString @ If[ LeafCount[HoldForm[f]] > 200, StringTake[ToString[f], UpTo[300]] <> "...", HoldForm[f] ] },
                    Echo[
                      TemplateApply[StringTemplate[MStateBind::ffail], ef], ToString[MStateBind] <> ":"]
                  ]
                ];
                MStateFailureSymbol,
                StringQ[res[[2]]], res,
                MatchQ[res, MState[_, _]], MStateContexts[context] = res[[2]]; MState[res[[1]], context],
                True, MStateFailureSymbol
              ]
            ];
      ];
      MStateBind[___] := MStateFailureSymbol;
      MStateBind::usage = "Monad binding function.";

      MStateEcho[MStateFailureSymbol] := MStateFailureSymbol;
      MStateEcho[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateEcho[echoArgs__][x_, context_Association] := (Echo[echoArgs]; MState[x, context]);
      MStateEcho[x_, context_Association] := (Echo[Short[MState[x, context]]]; MState[x, context]);
      MStateEcho[][x_, context_Association] := MStateEcho[x, context];
      MStateEcho::usage = "Echoes the argument. If no argument is given the short print of the monad object is echoed.";


      MStateEchoValue[MStateFailureSymbol] := (Echo[MStateFailureSymbol]; MStateFailureSymbol);
      MStateEchoValue[x_, context_Association] := (Echo[x, "value:"]; MState[x, context]);

      MStateEchoValue[][MStateFailureSymbol] := MStateEchoValue[MStateFailureSymbol];
      MStateEchoValue[][x_, context_Association] := MStateEchoValue[x, context];
      MStateEchoValue::usage = "Echoes the monad value.";


      MStateEchoFunctionValue[f___][MStateFailureSymbol] := (Echo[MStateFailureSymbol]; MStateFailureSymbol);
      MStateEchoFunctionValue[f___][x_, context_Association] := (EchoFunction[f][x]; MState[x, context]);
      MStateEchoFunctionValue::usage = "Echoes function application over the monad value.";


      MStateEchoContext[MStateFailureSymbol] := (Echo[MStateFailureSymbol]; MStateFailureSymbol);
      MStateEchoContext[x_, context_Association] := (Echo[context, "context:"]; MState[x, context]);

      MStateEchoContext[][MStateFailureSymbol] := MStateEchoContext[MStateFailureSymbol];
      MStateEchoContext[][x_, context_Association] := MStateEchoContext[x, context];
      MStateEchoContext::usage = "Echoes the monad context.";


      MStateEchoFunctionContext[f_][MStateFailureSymbol] := MStateFailureSymbol;
      MStateEchoFunctionContext[f___][x_, context_Association] := (EchoFunction[f][context]; MState[x, context]);
      MStateEchoFunctionContext::usage = "Echoes function application over the monad context.";


      MStateAssignTo[___][MStateFailureSymbol] := MStateFailureSymbol;
      SetAttributes[MStateAssignTo, HoldFirst];
      MStateAssignTo[s_Symbol][x_, context_] := Set[s, MStateUnit[x, context]];
      MStateAssignTo::usage = "Assigns the monad object to the argument.";

      MStateAssignContextTo[___][MStateFailureSymbol] := MStateFailureSymbol;
      SetAttributes[MStateAssignContextTo, HoldFirst];
      MStateAssignContextTo[s_Symbol][x_, context_] := Set[s, context];
      MStateAssignContextTo::usage = "Assigns the monad context to the argument.";

      MStateAssignValueTo[___][MStateFailureSymbol] := MStateFailureSymbol;
      SetAttributes[MStateAssignValueTo, HoldFirst];
      MStateAssignValueTo[s_Symbol][x_, context_] := Set[s, x];
      MStateAssignValueTo::usage = "Assigns the monad value to the argument.";


      MStateTakeValue[MStateFailureSymbol] := MStateFailureSymbol;
      MStateTakeValue[x_, context_] := x;

      MStateTakeValue[][MStateFailureSymbol] := MStateFailureSymbol;
      MStateTakeValue[][x_, context_] := x;
      MStateTakeValue::usage = "Takes the monad value.";


      MStateTakeContext[MStateFailureSymbol] := MStateFailureSymbol;
      MStateTakeContext[x_, context_] := context;

      MStateTakeContext[][MStateFailureSymbol] := MStateFailureSymbol;
      MStateTakeContext[][x_, context_] := context;
      MStateTakeContext::usage = "Takes the monad context.";


      MStatePutContext[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStatePutContext[newContext_Association][x_, context_Association] := MState[x, newContext];
      If[TrueQ[OptionValue["StringContextNames"]],
        MStatePutContext[newContext_String][x_, context_Association] :=
            If[! MatchQ[MStateContexts[newContext], _Association],
              Echo[TemplateApply[StringTemplate[MStateContexts::nocxt], newContext]];
              MStateFailureSymbol,
              MState[x, newContext]
            ];
      ];
      MStatePutContext::usage = "Replaces the monad context with the argument.";

      MStateSetContext = MStatePutContext;
      MStateSetContext::usage = MStatePutContext::usage;


      MStatePutValue[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStatePutValue[newValue_][x_, context_] := MState[newValue, context];
      MStatePutValue::usage = "Replaces the monad value with the argument.";

      MStateSetValue = MStatePutValue;
      MStateSetValue::usage = MStatePutValue::usage;


      MStateModifyContext[f_][MStateFailureSymbol] := MStateFailureSymbol;
      MStateModifyContext[f_][x_, context_Association] := MState[x, f[context]];
      MStateModifyContext::usage = SymbolName[MState] <> "ModifyContext[f] replaces the monad context f[context].";


      MStateAddToContext[MStateFailureSymbol] := MStateFailureSymbol;
      MStateAddToContext[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateAddToContext[varName_String][x_, context_Association] := MState[x, Join[context, <|varName -> x|>]];
      MStateAddToContext[][x_Association, context_Association] := MState[{}, Join[context, x]];
      MStateAddToContext[x_Association, context_Association] := MState[{}, Join[context, x]];
      MStateAddToContext[arg_Association][x_, context_Association] := MState[x, Join[context, arg]];
      MStateAddToContext::usage =
          SymbolName[MState] <> "AddToContext[varName_String] adds to the monad context the monad value under key varName.\n" <>
              SymbolName[MState] <> "AddToContext[arg_Association] joins the monad context with arg.\n" <>
              SymbolName[MState] <> "AddToContext[] joins the monad context with the monad value.";


      MStateRetrieveFromContext[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateRetrieveFromContext[varName_String][x_, context_Association] := MState[context[varName], context];
      MStateRetrieveFromContext::usage =
          SymbolName[MState] <> "RetrieveFromContext[varName_String] retrieves from the monad context the value of the key varName.";


      MStateDropFromContext[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateDropFromContext[varNames : (_String | {_String..})][x_, context_Association] := MState[x, KeyDrop[context, varNames]];
      MStateDropFromContext::usage = "Drop from the monad context elements withe specified keys.";


      MStateOption[f_][MStateFailureSymbol] := MStateFailureSymbol;
      MStateOption[f_][xs_, context_] :=
          Block[{res = f[xs, context]}, If[FreeQ[res, MStateFailureSymbol], res, MState[xs, context]]];
      MStateOption::usage =
          "If the application of the argument to the monad produces monad failure the monad is unchanged.";


      MStateIfElse[testFunc_, fYes_, fNo_][MStateFailureSymbol] := MStateFailureSymbol;
      MStateIfElse[testFunc_, fYes_, fNo_][xs_, context_] :=
          Block[{testRes = testFunc[xs, context]},
            If[TrueQ[testRes], fYes[xs, context], fNo[xs, context]]
          ];
      MStateIfElse::usage =
          SymbolName[MState] <> "IfElse[testFunc_, fYes_, fNo_] executes fYes[xs, context] if TrueQ[testFunc[xs, context]]; otherwise fNo[xs, context].";


      MStateWhen[testFunc_, f_][MStateFailureSymbol] := MStateFailureSymbol;
      MStateWhen[testFunc_, f_][xs_, context_] := MStateIfElse[testFunc, f, MStateUnit][xs, context];
      MStateWhen::usage = "Shorter version of " <> SymbolName[MState] <> "IfElse.";


      (* Iteration functions *)
      MStateIterate[___][___] := MStateFailureSymbol;

      MStateIterate[itFunc : (Nest | NestWhile | FixedPoint), f_, args___][x_, context_Association] :=
          itFunc[MStateBind[#, f] &, MStateUnit[x, context], args];

      MStateIterate[itFunc : (NestList | NestWhileList | FixedPointList),
        f_, args___, contextVar : (None | _String) : None][x_, context_Association] :=
          Block[{res},
            res = itFunc[MStateBind[#, f] &, MStateUnit[x, context], args];
            If[contextVar === None,
              MStateUnit[res[[All, 1]], res[[-1, 2]]],
              (*ELSE*)
              MStateUnit[res[[All, 1]], Join[res[[-1, 2]], <|contextVar -> res|>]]
            ]
          ];

      MStateIterate[itFunc : (Fold | FoldList | Composition[__, FoldList]),
        f_, args___][x_, context_Association] :=
          itFunc[f, MStateUnit[x, context], args];

      (* Flow functions  with non-monadic function argument *)
      (* If, Nest, NestWhile, Fold *)
      MStateIf[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateIf[f_, fYes_][xs_, context_] := If[f[MStateUnit[xs, context]], fYes[MStateUnit[xs, context]]];
      MStateIf[f_, fYes_, fNo_][xs_, context_] :=
          If[f[MStateUnit[xs, context]],
            fYes[MStateUnit[xs, context]],
            fNo[MStateUnit[xs, context]]
          ];
      MStateIf[f_, fYes_, fNo_, fMu_][xs_, context_] :=
          If[f[MStateUnit[xs, context]],
            fYes[MStateUnit[xs, context]],
            fNo[MStateUnit[xs, context]],
            fMu[MStateUnit[xs, context]]
          ];
      MStateIf[___][xs_, context : (_Association | _String)] := MStateFailureSymbol;
      MStateIf::usage = SymbolName[MStateIf] <> "[f_, fYes_, fNo_] executes fYes[" <> SymbolName[MStateUnit] <> "[xs,context]] if f[" <> SymbolName[MStateUnit] <> "[xs,context]] is True; fNo[" <> SymbolName[MStateUnit] <> "[xs,context]] otherwise.";

      MStateNest[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateNest[f_, n_Integer][xs_, context_] := Nest[f, MStateUnit[xs, context], n];

      MStateNestWhile[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateNestWhile[f_, args__][xs_, context_] := NestWhile[f, MStateUnit[xs, context], args];

      MStateFold[___][MStateFailureSymbol] := MStateFailureSymbol;
      MStateFold[f_, list_][xs_, context_] := Fold[f, MStateUnit[xs, context], list];

      Attributes[MStateModule] = HoldAll;
      MStateModule[body___][value_, context_Association] :=
          MState[AssociationModule[Join[context, <|"$Value" -> value|>], body], context];

      (* We should have an option for the pipeline symbol. *)
      (* This looks much more like a pipeline operator than (**): *)
      DoubleLongRightArrow[Global`x_?MStateUnitQ, Global`f_] := MStateBind[Global`x, Global`f];
      DoubleLongRightArrow[Global`x_, Global`y_, Global`z__] :=
          DoubleLongRightArrow[DoubleLongRightArrow[Global`x, Global`y], Global`z];

      (*Unprotect[NonCommutativeMultiply];*)
      (*ClearAttributes[NonCommutativeMultiply, Attributes[NonCommutativeMultiply]]*)
      (*MState /: NonCommutativeMultiply[MState[Global`x_], Global`f_] := MStateBind[MState[Global`x], Global`f];*)
      (*NonCommutativeMultiply[Global`x_, Global`y_, Global`z__] :=*)
      (*NonCommutativeMultiply[NonCommutativeMultiply[Global`x, Global`y], Global`z];*)

    ];


Clear[GenerateMonadSetter];
Options[GenerateMonadSetter] = {"FailureSymbol" -> None, "DecapitalizeElementName" -> True};
GenerateMonadSetter[monadName_String, elementName_String, opts : OptionsPattern[]] :=
    With[{
      MStateUnit = ToExpression[monadName <> "Unit"],
      MStateSetter = ToExpression[monadName <> "Set" <> Capitalize[elementName]],
      MStateFailureSymbol = OptionValue["FailureSymbol"],
      dElementName = If[ TrueQ[OptionValue["DecapitalizeElementName"]], Decapitalize[elementName], elementName ]
    },

      ClearAll[MStateSetter];

      MStateSetter[MStateFailureSymbol] := MStateFailureSymbol;
      MStateSetter[][MStateFailureSymbol] := MStateFailureSymbol;
      MStateSetter[xs_, context_] := MStateFailureSymbol;
      MStateSetter[arg_?AtomQ][xs_, context_] := MStateUnit[ xs, Join[ context, <|dElementName -> arg|> ] ];
      MStateSetter[arg_List][xs_, context_] := MStateUnit[ xs, Join[ context, <|dElementName -> arg|> ] ];
      MStateSetter[args__][xs_, context_] :=
          If[ Length[{args}] > 1,
            MStateSetter[{args}][xs, context],
            MStateUnit[ xs, Join[ context, <|dElementName -> args|> ] ]
          ];
      MStateSetter[__][___] := MStateFailureSymbol;

      MStateSetter::usage = "Assigns the argument to the key \"" <> dElementName <> "\" in the monad context."
    ];


Clear[GenerateMonadTaker];
Options[GenerateMonadTaker] = {"FailureSymbol" -> None, "DecapitalizeElementName" -> True};
GenerateMonadTaker[monadName_String, elementName_String, opts : OptionsPattern[]] :=
    With[{
      MState = ToExpression[monadName],
      MStateTaker = ToExpression[monadName <> "Take" <> Capitalize[elementName]],
      MStateFailureSymbol = OptionValue["FailureSymbol"],
      dElementName = If[ TrueQ[OptionValue["DecapitalizeElementName"]], Decapitalize[elementName], elementName ]
    },

      ClearAll[MStateTaker];

      MStateTaker[MStateFailureSymbol] := MStateFailureSymbol;
      MStateTaker[][MStateFailureSymbol] := MStateFailureSymbol;
      MStateTaker[xs_, context_] := context[dElementName];
      MStateTaker[][xs_, context_] := context[dElementName];
      MStateTaker[__][___] := MStateFailureSymbol;

      MStateTaker::usage = "Gives the value of the key \"" <> dElementName <> "\" from the monad context."
    ];


Clear[GenerateMonadDroper];
Options[GenerateMonadDroper] = {"FailureSymbol" -> None, "DecapitalizeElementName" -> True};
GenerateMonadDroper[monadName_String, elementName_String, opts : OptionsPattern[]] :=
    With[{
      MState = ToExpression[monadName],
      MStateDroper = ToExpression[monadName <> "Drop" <> Capitalize[elementName]],
      MStateFailureSymbol = OptionValue["FailureSymbol"],
      MStateDropFromContext = ToExpression[monadName <> "DropFromContext"],
      dElementName = If[ TrueQ[OptionValue["DecapitalizeElementName"]], Decapitalize[elementName], elementName ]
    },

      ClearAll[MStateDroper];

      MStateDroper[MStateFailureSymbol] := MStateFailureSymbol;
      MStateDroper[][MStateFailureSymbol] := MStateFailureSymbol;
      MStateDroper[xs_, context_] := MStateDroper[][xs, context];
      MStateDroper[][xs_, context_] := MStateDropFromContext[dElementName][xs, context];
      MStateDroper[__][___] := MStateFailureSymbol;

      MStateDroper::usage = "Drops from the context the element with key \"" <> dElementName <> "\"."
    ];


Clear[GenerateMonadAccessors];
Options[GenerateMonadAccessors] = Options[GenerateMonadSetter];
GenerateMonadAccessors[monadName_String, elementName_String, opts : OptionsPattern[]] :=
    GenerateMonadAccessors[monadName, {elementName}, opts ];
GenerateMonadAccessors[monadName_String, elementNames : {_String..}, opts : OptionsPattern[]] :=
    Block[{},
      Map[GenerateMonadSetter[monadName, #, opts]&, elementNames];
      Map[GenerateMonadTaker[monadName, #, opts]&, elementNames];
      Map[GenerateMonadDroper[monadName, #, opts]&, elementNames];
    ];

End[]; (* `Private` *)

EndPackage[]