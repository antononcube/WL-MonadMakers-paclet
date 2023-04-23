(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["AntonAntonov`MonadMakers`"];

GenerateStateMonadCode::usage = "GenerateStateMonadCode[monadName_String] generates the basic functions \
of a State monad that allows computations with a mutable context. Code for handling context string names \
is generated depending on the Boolean values of the option \"StringContextNames\". \
Monad's failure symbol is specified with the option \"FailureSymbol\".";

AssociationModule::usage = "AssociationModule[asc_Association, body_] transforms the elements of asc into \
symbol assignments ascAssign and executes Module[ ascAssign, body ]. The keys of asc are assumed to be strings.";

GenerateMonadDroper::usage = "GenerateMonadDroper[monadName_String, elementName_String] generates monadic \
droper functions for specified monad and element names.";

GenerateMonadSetter::usage = "GenerateMonadSetter[monadName_String, elementName_String] generates monadic \
setter functions for specified monad and element names.";

GenerateMonadTaker::usage = "GenerateMonadTaker[monadName_String, elementName_String] generates monadic \
taker functions for specified monad and element names.";

GenerateMonadAccessors::usage = "GenerateMonadAccessors[monadName_String, elementNames:{_String..}] generates monadic \
droper, setter, and taker functions for specified monad and element names.";


$TraceMonadFailure::usage = "Failure symbol for TraceMonad.";

TraceMonadUnit::usage = "Lifting a monad object into TraceMonad.";

TraceMonadBind::usage = "The binding function of TraceMonad.";

TraceMonadEchoGrid::usage = "Echoes a tabulation of the traced monad functions using Grid.";

TraceMonadTakeGrid::usage = "Gives a tabulation of the traced monad functions using Grid.";

Grid87::usage = "A modified version of Grid.";

TraceMonad;

Begin["`Private`"];

Needs["AntonAntonov`MonadMakers`StateMonadGenerator`"];
Needs["AntonAntonov`MonadMakers`MonadTracer`"];


End[];
EndPackage[];